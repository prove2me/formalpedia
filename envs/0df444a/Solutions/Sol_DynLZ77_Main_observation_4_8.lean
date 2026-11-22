-- Prove2me | solution 1 for DynLZ77.Main.observation_4_8
-- status  : ACCEPTED   (prove)
-- author  : @shaygo
-- created : 2026-11-22T05:32:07.344679+00:00
-- url     : https://prove2.me/submissions/5641a04b-b775-4fa0-ade8-f3efea3c671e

import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Card
import Definitions.Def_DynLZ77_Main_Strings
import Definitions.Def_DynLZ77_Main_Structure

set_option autoImplicit false

/-! ## Auxiliary lemmas on `lcp`, `lpf`, the LZ77 scan and the LPF′-tree -/

namespace DynLZ77.Main.Aux

section NoDecEq

variable {α : Type}

/-- Two lists agreeing on a prefix of length `L` agree on every window inside that prefix. -/
theorem take_drop_eq_of_take_eq {u v : List α} {L d t : ℕ} (h : u.take L = v.take L)
    (hdt : d + t ≤ L) : (u.drop d).take t = (v.drop d).take t := by
  have key : ∀ w : List α, (w.drop d).take t = ((w.take L).take (d + t)).drop d := by
    intro w
    rw [List.take_take, Nat.min_eq_left hdt, List.drop_take, Nat.add_sub_cancel_left]
  rw [key u, key v, h]

theorem phraseStart_cons_zero (w : List α) (ws : List (List α)) : phraseStart (w :: ws) 0 = 1 := by
  simp only [phraseStart, List.take_zero, List.map_nil, List.sum_nil]

theorem phraseStart_cons_succ (w : List α) (ws : List (List α)) (t : ℕ) :
    phraseStart (w :: ws) (t + 1) = w.length + phraseStart ws t := by
  simp only [phraseStart, List.take_succ_cons, List.map_cons, List.sum_cons]
  omega

end NoDecEq

variable {α : Type} [DecidableEq α]

/-! ### Longest common prefix -/

theorem lcp_cons_cons (a b : α) (u v : List α) :
    lcp (a :: u) (b :: v) = if a = b then lcp u v + 1 else 0 := rfl

theorem lcp_nil_left (v : List α) : lcp [] v = 0 := by cases v <;> rfl

theorem lcp_nil_right (u : List α) : lcp u [] = 0 := by cases u <;> rfl

/-- `ℓ ≤ LCP(u, v)` iff both lists have length at least `ℓ` and agree on their first `ℓ`
letters. -/
theorem le_lcp_iff : ∀ (ℓ : ℕ) (u v : List α),
    ℓ ≤ lcp u v ↔ ℓ ≤ u.length ∧ ℓ ≤ v.length ∧ u.take ℓ = v.take ℓ
  | 0, u, v => by simp
  | ℓ + 1, [], v => by simp [lcp_nil_left]
  | ℓ + 1, a :: u, [] => by simp [lcp_nil_right]
  | ℓ + 1, a :: u, b :: v => by
      rw [lcp_cons_cons]
      by_cases h : a = b
      · subst h
        simp [le_lcp_iff ℓ u v]
      · simp [h]

theorem lcp_le_length_left (u v : List α) : lcp u v ≤ u.length :=
  ((le_lcp_iff _ u v).1 le_rfl).1

theorem lcp_tail_tail (u v : List α) : lcp u v - 1 ≤ lcp u.tail v.tail := by
  cases u with
  | nil => rw [lcp_nil_left]; exact Nat.zero_le _
  | cons a u =>
    cases v with
    | nil => rw [lcp_nil_right]; exact Nat.zero_le _
    | cons b v =>
      rw [lcp_cons_cons]
      split_ifs
      · simp only [List.tail_cons, Nat.add_sub_cancel, le_refl]
      · exact Nat.zero_le _

/-! ### Longest previous factor -/

theorem lcpAt_le_lpf (S : List α) {i j : ℕ} (hj1 : 1 ≤ j) (hji : j < i) :
    lcpAt S i j ≤ lpf S i :=
  Finset.le_sup (f := fun j => lcpAt S i j) (Finset.mem_Ico.2 ⟨hj1, hji⟩)

theorem lpf_le (S : List α) (i : ℕ) : lpf S i ≤ S.length - (i - 1) :=
  Finset.sup_le fun j _ => by
    have h := lcp_le_length_left (S.drop (i - 1)) (S.drop (j - 1))
    rw [List.length_drop] at h
    exact h

theorem lpf_zero (S : List α) : lpf S 0 = 0 := by
  unfold lpf
  rw [Finset.Ico_eq_empty_of_le (Nat.zero_le 1), Finset.sup_empty]
  rfl

theorem exists_lpf (S : List α) {i : ℕ} (h : 0 < lpf S i) :
    ∃ j, 1 ≤ j ∧ j < i ∧ lcpAt S i j = lpf S i := by
  by_cases hi : 1 < i
  · obtain ⟨j, hj, hj'⟩ := Finset.exists_mem_eq_sup (Finset.Ico 1 i)
      (Finset.nonempty_Ico.2 hi) (fun j => lcpAt S i j)
    rw [Finset.mem_Ico] at hj
    exact ⟨j, hj.1, hj.2, hj'.symm⟩
  · have h0 : lpf S i = 0 := by
      unfold lpf
      rw [Finset.Ico_eq_empty_of_le (by omega), Finset.sup_empty]
      rfl
    omega

theorem take_eq_of_lcpAt (S : List α) {i j L : ℕ} (h : lcpAt S i j = L) :
    (S.drop (j - 1)).take L = (S.drop (i - 1)).take L :=
  ((le_lcp_iff L _ _).1 (le_of_eq h.symm)).2.2.symm

/-- A factor `S[i..i+ℓ)` inside `S` that also starts at `j ∈ [1..i)` has length at most
`LPF_S(i)`. -/
theorem le_lpf_of_take (S : List α) {i j ℓ : ℕ} (hj1 : 1 ≤ j) (hji : j < i)
    (hlen : i - 1 + ℓ ≤ S.length)
    (heq : (S.drop (j - 1)).take ℓ = (S.drop (i - 1)).take ℓ) : ℓ ≤ lpf S i := by
  refine le_trans ?_ (lcpAt_le_lpf S hj1 hji)
  show ℓ ≤ lcp (S.drop (i - 1)) (S.drop (j - 1))
  refine (le_lcp_iff ℓ _ _).2 ⟨?_, ?_, heq.symm⟩ <;> (rw [List.length_drop]; omega)

/-! ### Lemma 4.5 and monotonicity of the LPF′-tree parent map -/

theorem lpf_sub_one_le (S : List α) {i : ℕ} (hi : 1 ≤ i) : lpf S i - 1 ≤ lpf S (i + 1) := by
  rcases Nat.eq_zero_or_pos (lpf S i) with h | h
  · omega
  · obtain ⟨j, hj1, hji, hjeq⟩ := exists_lpf S h
    have key : lcpAt S i j - 1 ≤ lcpAt S (i + 1) (j + 1) := by
      have h' := lcp_tail_tail (S.drop (i - 1)) (S.drop (j - 1))
      rw [List.tail_drop, List.tail_drop] at h'
      have e1 : i - 1 + 1 = i + 1 - 1 := by omega
      have e2 : j - 1 + 1 = j + 1 - 1 := by omega
      rw [e1, e2] at h'
      exact h'
    rw [← hjeq]
    exact key.trans (lcpAt_le_lpf S (by omega) (by omega))

theorem lt_add_lpf' (S : List α) (i : ℕ) : i < i + lpf' S i := by
  have := le_max_right (lpf S i) 1
  unfold lpf'
  omega

theorem add_lpf'_le (S : List α) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ S.length) :
    i + lpf' S i ≤ S.length + 1 := by
  have := lpf_le S i
  simp only [lpf', max_def]
  split_ifs <;> omega

/-- Lemma 4.5 for every `i : ℕ`. -/
theorem add_lpf'_le_succ (S : List α) (i : ℕ) : i + lpf' S i ≤ i + 1 + lpf' S (i + 1) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have h0 : lpf' S 0 = 1 := by
      unfold lpf'
      rw [lpf_zero]
      rfl
    have := le_max_right (lpf S (0 + 1)) 1
    unfold lpf' at *
    omega
  · have := lpf_sub_one_le S hi
    simp only [lpf', max_def]
    split_ifs <;> omega

theorem treeParent_mono (S : List α) : Monotone (treeParent S) :=
  monotone_nat_of_le_succ fun i => by
    have := add_lpf'_le_succ S i
    simp only [treeParent]
    omega

/-! ### The LZ77 scan and the depth function -/

theorem lz77From_of_mem (S : List α) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ S.length) :
    lz77From S i = (i, i + lpf' S i - 1) :: lz77From S (i + lpf' S i) := by
  rw [lz77From, if_pos ⟨h1, h2⟩]

theorem lz77From_of_not (S : List α) {i : ℕ} (h : ¬ (1 ≤ i ∧ i ≤ S.length)) :
    lz77From S i = [] := by
  rw [lz77From, if_neg h]

theorem depth_of_mem (S : List α) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ S.length) :
    depth S i = depth S (i + lpf' S i) + 1 := by
  rw [depth, if_pos ⟨h1, h2⟩]

theorem depth_of_not (S : List α) {i : ℕ} (h : ¬ (1 ≤ i ∧ i ≤ S.length)) : depth S i = 0 := by
  rw [depth, if_neg h]

theorem length_lz77From (S : List α) (i : ℕ) : (lz77From S i).length = depth S i := by
  by_cases h : 1 ≤ i ∧ i ≤ S.length
  · rw [lz77From_of_mem S h.1 h.2, depth_of_mem S h.1 h.2, List.length_cons,
      length_lz77From S (i + lpf' S i)]
  · rw [lz77From_of_not S h, depth_of_not S h, List.length_nil]
termination_by S.length + 1 - i
decreasing_by
  have := lt_add_lpf' S i
  omega

theorem iterate_depth (S : List α) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ S.length + 1) :
    (treeParent S)^[depth S i] i = S.length + 1 := by
  by_cases h : 1 ≤ i ∧ i ≤ S.length
  · rw [depth_of_mem S h.1 h.2, Function.iterate_succ_apply]
    exact iterate_depth S (i + lpf' S i) (by omega) (add_lpf'_le S h.1 h.2)
  · rw [depth_of_not S h, Function.iterate_zero_apply]
    omega
termination_by S.length + 1 - i
decreasing_by
  have := lt_add_lpf' S i
  omega

theorem lz77From_getElem? (S : List α) : ∀ (m i : ℕ), m < (lz77From S i).length →
    (lz77From S i)[m]? = some ((treeParent S)^[m] i,
      (treeParent S)^[m] i + lpf' S ((treeParent S)^[m] i) - 1)
  | 0, i, h => by
      have hi : 1 ≤ i ∧ i ≤ S.length := by
        by_contra hi
        rw [lz77From_of_not S hi, List.length_nil] at h
        omega
      rw [lz77From_of_mem S hi.1 hi.2, List.getElem?_cons_zero, Function.iterate_zero_apply]
  | m + 1, i, h => by
      have hi : 1 ≤ i ∧ i ≤ S.length := by
        by_contra hi
        rw [lz77From_of_not S hi, List.length_nil] at h
        omega
      rw [lz77From_of_mem S hi.1 hi.2, List.length_cons] at h
      rw [lz77From_of_mem S hi.1 hi.2, List.getElem?_cons_succ,
        lz77From_getElem? S m (i + lpf' S i) (by omega)]
      rfl

/-! ### Phrase starts of the LZ77 scan -/

theorem mem_starts_iff (S : List α) {p x : ℕ} (h1 : 1 ≤ p) (h2 : p ≤ S.length) :
    x ∈ (lz77From S p).map Prod.fst ↔ x = p ∨ x ∈ (lz77From S (p + lpf' S p)).map Prod.fst := by
  rw [lz77From_of_mem S h1 h2, List.map_cons, List.mem_cons]

theorem not_mem_starts (S : List α) {p x : ℕ} (h : ¬ (1 ≤ p ∧ p ≤ S.length)) :
    x ∉ (lz77From S p).map Prod.fst := by
  rw [lz77From_of_not S h, List.map_nil]
  exact List.not_mem_nil

theorem starts_bounds (S : List α) (p : ℕ) (hp : 1 ≤ p) :
    ∀ x, x ∈ (lz77From S p).map Prod.fst → p ≤ x ∧ x ≤ S.length := by
  intro x hx
  by_cases h : 1 ≤ p ∧ p ≤ S.length
  · rcases (mem_starts_iff S h.1 h.2).1 hx with hxp | hx'
    · rw [hxp]
      exact ⟨le_rfl, h.2⟩
    · have := starts_bounds S (p + lpf' S p) (by omega) x hx'
      have := lt_add_lpf' S p
      omega
  · exact absurd hx (not_mem_starts S h)
termination_by S.length + 1 - p
decreasing_by
  have := lt_add_lpf' S p
  omega

/-- The successor `x + LPF′(x)` of a phrase start is the next phrase start (if it is `≤ n`). -/
theorem starts_succ (S : List α) (p : ℕ) (hp : 1 ≤ p) :
    ∀ x, x ∈ (lz77From S p).map Prod.fst → x + lpf' S x ≤ S.length →
      x + lpf' S x ∈ (lz77From S p).map Prod.fst := by
  intro x hx hfx
  by_cases h : 1 ≤ p ∧ p ≤ S.length
  · rw [mem_starts_iff S h.1 h.2] at hx ⊢
    rcases hx with hxp | hx'
    · right
      rw [hxp] at hfx ⊢
      rw [mem_starts_iff S (by have := lt_add_lpf' S p; omega) hfx]
      exact Or.inl rfl
    · exact Or.inr (starts_succ S (p + lpf' S p) (by omega) x hx' hfx)
  · exact absurd hx (not_mem_starts S h)
termination_by S.length + 1 - p
decreasing_by
  have := lt_add_lpf' S p
  omega

/-- Between a phrase start `x` and a later phrase start `y` lies the whole phrase of `x`. -/
theorem starts_gap (S : List α) (p : ℕ) (hp : 1 ≤ p) :
    ∀ x y, x ∈ (lz77From S p).map Prod.fst → y ∈ (lz77From S p).map Prod.fst → x < y →
      x + lpf' S x ≤ y := by
  intro x y hx hy hxy
  by_cases h : 1 ≤ p ∧ p ≤ S.length
  · rw [mem_starts_iff S h.1 h.2] at hx hy
    rcases hx with hxp | hx'
    · rcases hy with hyp | hy'
      · omega
      · rw [hxp]
        exact (starts_bounds S _ (by omega) y hy').1
    · rcases hy with hyp | hy'
      · have := (starts_bounds S _ (by omega) x hx').1
        have := lt_add_lpf' S p
        omega
      · exact starts_gap S (p + lpf' S p) (by omega) x y hx' hy' hxy
  · exact absurd hx (not_mem_starts S h)
termination_by S.length + 1 - p
decreasing_by
  have := lt_add_lpf' S p
  omega

/-! ### LZ-like parsings with an offset -/

/-- `Good X q P`: the phrases `P` parse `X.drop q` (positions `q+1, q+2, …` of `X`), each
nonempty and a single character or a copy of an occurrence starting earlier in `X`. -/
def Good (X : List α) (q : ℕ) (P : List (List α)) : Prop :=
  P.flatten = X.drop q ∧ ∀ (t : ℕ) (ht : t < P.length), P[t] ≠ [] ∧
    (P[t].length = 1 ∨ ∃ a' : ℕ, 1 ≤ a' ∧ a' < q + phraseStart P t ∧
      (X.drop (a' - 1)).take P[t].length = P[t])

omit [DecidableEq α] in
theorem isLZLike_of_good {X : List α} {P : List (List α)} (h : Good X 0 P) : IsLZLike X P := by
  refine ⟨by simpa only [List.drop_zero] using h.1, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 t ht
  exact ⟨h1, by simpa only [Nat.zero_add] using h2⟩

omit [DecidableEq α] in
theorem good_of_isLZLike {X : List α} {P : List (List α)} (h : IsLZLike X P) : Good X 0 P := by
  refine ⟨by simpa only [List.drop_zero] using h.1, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := h.2 t ht
  exact ⟨h1, by simpa only [Nat.zero_add] using h2⟩

omit [DecidableEq α] in
theorem good_nil_iff (X : List α) (q : ℕ) : Good X q [] ↔ X.drop q = [] := by
  constructor
  · intro h
    exact h.1.symm
  · intro h
    exact ⟨h.symm, fun t ht => (Nat.not_lt_zero t ht).elim⟩

omit [DecidableEq α] in
theorem good_cons_iff (X : List α) (q : ℕ) (w : List α) (ws : List (List α)) :
    Good X q (w :: ws) ↔ w ≠ [] ∧ (X.drop q).take w.length = w ∧
      (w.length = 1 ∨ ∃ a' : ℕ, 1 ≤ a' ∧ a' < q + 1 ∧ (X.drop (a' - 1)).take w.length = w) ∧
      Good X (q + w.length) ws := by
  constructor
  · rintro ⟨hfl, hall⟩
    have hfl' : w ++ ws.flatten = X.drop q := by rw [← hfl, List.flatten_cons]
    have htake : (X.drop q).take w.length = w := by
      rw [← hfl']
      exact List.take_left
    have hdrop : ws.flatten = X.drop (q + w.length) := by
      rw [← List.drop_drop, ← hfl']
      exact List.drop_left.symm
    obtain ⟨h0ne, h0⟩ := hall 0 (Nat.succ_pos _)
    refine ⟨h0ne, htake, ?_, hdrop, ?_⟩
    · rw [phraseStart_cons_zero] at h0
      exact h0
    · intro t ht
      obtain ⟨hne, h⟩ := hall (t + 1) (by rw [List.length_cons]; omega)
      rw [phraseStart_cons_succ] at h
      refine ⟨hne, ?_⟩
      rcases h with h | ⟨a', h1, h2, h3⟩
      · exact Or.inl h
      · exact Or.inr ⟨a', h1, by omega, h3⟩
  · rintro ⟨hne, htake, hsrc, hfl, hall⟩
    refine ⟨?_, ?_⟩
    · rw [List.flatten_cons, hfl, ← List.drop_drop]
      conv_rhs => rw [← List.take_append_drop w.length (X.drop q)]
      rw [htake]
    · intro t ht
      cases t with
      | zero =>
        refine ⟨hne, ?_⟩
        rw [phraseStart_cons_zero]
        exact hsrc
      | succ t =>
        obtain ⟨hne', h⟩ := hall t (by rw [List.length_cons] at ht; omega)
        refine ⟨hne', ?_⟩
        rw [phraseStart_cons_succ]
        rcases h with h | ⟨a', h1, h2, h3⟩
        · exact Or.inl h
        · exact Or.inr ⟨a', h1, by omega, h3⟩

/-- The phrases of the LZ77 scan from position `i` parse `X.drop (i - 1)` LZ-like. -/
theorem lz77From_good (X : List α) (i : ℕ) (h1 : 1 ≤ i) (h2 : i ≤ X.length + 1) :
    Good X (i - 1) ((lz77From X i).map (fun ab => sub X ab.1 ab.2)) := by
  by_cases h : 1 ≤ i ∧ i ≤ X.length
  · rw [lz77From_of_mem X h.1 h.2, List.map_cons]
    have hle := add_lpf'_le X h.1 h.2
    have hL : 1 ≤ lpf' X i := le_max_right _ _
    have hsub : sub X i (i + lpf' X i - 1) = (X.drop (i - 1)).take (lpf' X i) := by
      unfold sub
      congr 1
      omega
    have hlen : ((X.drop (i - 1)).take (lpf' X i)).length = lpf' X i := by
      rw [List.length_take, List.length_drop]
      omega
    dsimp only
    rw [hsub, good_cons_iff]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h0
      rw [h0, List.length_nil] at hlen
      omega
    · rw [hlen]
    · rw [hlen]
      by_cases h0 : lpf X i = 0
      · left
        unfold lpf'
        rw [h0]
        rfl
      · right
        obtain ⟨j, hj1, hji, hjeq⟩ := exists_lpf X (Nat.pos_of_ne_zero h0)
        have hmax : lpf' X i = lpf X i := max_eq_left (Nat.one_le_iff_ne_zero.2 h0)
        refine ⟨j, hj1, by omega, ?_⟩
        rw [hmax]
        exact take_eq_of_lcpAt X hjeq
    · rw [hlen]
      have e : i - 1 + lpf' X i = i + lpf' X i - 1 := by omega
      rw [e]
      exact lz77From_good X (i + lpf' X i) (by omega) hle
  · have hi : i = X.length + 1 := by omega
    rw [lz77From_of_not X h, List.map_nil, good_nil_iff, hi, Nat.add_sub_cancel]
    exact List.drop_length
termination_by X.length + 1 - i
decreasing_by
  have := lt_add_lpf' X i
  omega

/-- An LZ-like phrase starting at position `p` ends no later than the LZ77 phrase at `p`. -/
theorem valid_le (X : List α) {p : ℕ} {w : List α} (hw : w ≠ [])
    (htake : (X.drop (p - 1)).take w.length = w)
    (hsrc : w.length = 1 ∨ ∃ a' : ℕ, 1 ≤ a' ∧ a' < p ∧ (X.drop (a' - 1)).take w.length = w) :
    p + w.length ≤ p + lpf' X p := by
  rcases hsrc with h1 | ⟨a', ha1, ha2, ha3⟩
  · rw [h1]
    have := le_max_right (lpf X p) 1
    unfold lpf'
    omega
  · have hpos : 0 < w.length := List.length_pos_iff.2 hw
    have hlen : p - 1 + w.length ≤ X.length := by
      have h := congrArg List.length htake
      rw [List.length_take, List.length_drop] at h
      omega
    have h1 := le_lpf_of_take X ha1 ha2 hlen (ha3.trans htake.symm)
    have h2 := le_max_left (lpf X p) 1
    unfold lpf'
    omega

/-- Greedy stays ahead: the LZ77 scan from `p` needs no more phrases than an LZ-like parsing of
`X.drop q` with `q + 1 ≤ p`. -/
theorem length_lz77From_le (X : List α) : ∀ (P : List (List α)) (p q : ℕ),
    Good X q P → q + 1 ≤ p → (lz77From X p).length ≤ P.length
  | [], p, q, h, hqp => by
      have hq : X.length ≤ q := List.drop_eq_nil_iff.1 ((good_nil_iff X q).1 h)
      rw [lz77From_of_not X (by omega), List.length_nil]
      exact Nat.zero_le _
  | w :: ws, p, q, h, hqp => by
      obtain ⟨hw, htake, hsrc, hrest⟩ := (good_cons_iff X q w ws).1 h
      by_cases hp : 1 ≤ p ∧ p ≤ X.length
      · rw [lz77From_of_mem X hp.1 hp.2, List.length_cons, List.length_cons]
        have h1 := valid_le X (p := q + 1) hw (by rw [Nat.add_sub_cancel]; exact htake) hsrc
        have h2 := treeParent_mono X hqp
        simp only [treeParent] at h2
        exact Nat.succ_le_succ
          (length_lz77From_le X ws (p + lpf' X p) (q + w.length) hrest (by omega))
      · rw [lz77From_of_not X hp, List.length_nil]
        exact Nat.zero_le _

/-! ### Fact 8.9 -/

theorem exists_start (S : List α) {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j) (hj : j ≤ S.length)
    (hnew : ∀ i' : ℕ, 1 ≤ i' → i' < i → sub S i' (i' + (j - i)) ≠ sub S i j)
    (p : ℕ) (hp1 : 1 ≤ p) (hpi : p ≤ i) :
    ∃ x y : ℕ, (x, y) ∈ lz77From S p ∧ i ≤ x ∧ x ≤ j := by
  rw [lz77From_of_mem S hp1 (by omega)]
  rcases Nat.eq_or_lt_of_le hpi with hpi' | hlt
  · exact ⟨p, _, List.mem_cons_self, by omega, by omega⟩
  · by_cases hm : p + lpf' S p ≤ i
    · obtain ⟨x, y, hxy, h1, h2⟩ := exists_start S hi hij hj hnew (p + lpf' S p) (by omega) hm
      exact ⟨x, y, List.mem_cons_of_mem _ hxy, h1, h2⟩
    · by_cases hmj : p + lpf' S p ≤ j
      · rw [lz77From_of_mem S (i := p + lpf' S p) (by omega) (by omega)]
        exact ⟨_, _, List.mem_cons_of_mem _ List.mem_cons_self, by omega, hmj⟩
      · exfalso
        have hL : 2 ≤ lpf' S p := by omega
        have hpos : 0 < lpf S p := by
          unfold lpf' at hL
          rcases le_total (lpf S p) 1 with h | h
          · rw [max_eq_right h] at hL
            omega
          · omega
        have hmax : lpf' S p = lpf S p := max_eq_left (by omega)
        obtain ⟨i', hi'1, hi'p, hi'eq⟩ := exists_lpf S hpos
        have htake := take_eq_of_lcpAt S hi'eq
        have key := take_drop_eq_of_take_eq htake (d := i - p) (t := j + 1 - i) (by omega)
        rw [List.drop_drop, List.drop_drop] at key
        have e1 : p - 1 + (i - p) = i - 1 := by omega
        have e2 : i' - 1 + (i - p) = i' + (i - p) - 1 := by omega
        rw [e1, e2] at key
        apply hnew (i' + (i - p)) (by omega) (by omega)
        unfold sub
        have e3 : i' + (i - p) + (j - i) + 1 - (i' + (i - p)) = j + 1 - i := by omega
        rw [e3]
        exact key
termination_by i - p
decreasing_by
  have := lt_add_lpf' S p
  omega

/-! ### Internal nodes of the LPF′-tree versus irreducible positions -/

theorem exists_Ired (S : List α) :
    ∀ i, 1 ≤ i → i ≤ S.length → ∃ r ∈ Ired S, treeParent S r = treeParent S i
  | 0, h, _ => absurd h (by omega)
  | 1, _, hn => by
      refine ⟨1, ?_, rfl⟩
      rw [Ired, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨le_rfl, hn⟩, Or.inl rfl⟩
  | m + 2, _, hn => by
      by_cases hm : m + 2 + lpf' S (m + 2) ≠ m + 2 - 1 + lpf' S (m + 2 - 1)
      · refine ⟨m + 2, ?_, rfl⟩
        rw [Ired, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, hn⟩, Or.inr hm⟩
      · replace hm := Classical.not_not.1 hm
        have e : m + 2 - 1 = m + 1 := by omega
        rw [e] at hm
        obtain ⟨r, hr, hreq⟩ := exists_Ired S (m + 1) (by omega) (by omega)
        exact ⟨r, hr, hreq.trans (by simp only [treeParent]; omega)⟩

/-- The internal nodes of the LPF′-tree number at most `|Ired_S|`. -/
theorem card_internalNodes_le (S : List α) : (internalNodes S).card ≤ (Ired S).card := by
  have hsub : internalNodes S ⊆ (Ired S).image (treeParent S) := by
    intro x hx
    rw [internalNodes, Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_Icc] at hi
    obtain ⟨r, hr, hreq⟩ := exists_Ired S i hi.1 hi.2
    exact Finset.mem_image.2 ⟨r, hr, hreq⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

end DynLZ77.Main.Aux

open DynLZ77.Main

/-- **Observation 4.8** (p. 18). The path from node `1` to the root of the LPF′-tree spells
`LZ77(S)`. -/
theorem solution {α : Type} [DecidableEq α] (S : List α) :
    pathNode S (depth S 1) = S.length + 1 ∧ depth S 1 = (LZ77 S).length ∧
      ∀ k : ℕ, 1 ≤ k → k ≤ depth S 1 →
        (LZ77 S)[k - 1]? =
          some (pathNode S (k - 1), pathNode S (k - 1) + lpf' S (pathNode S (k - 1)) - 1) := by
  refine ⟨Aux.iterate_depth S 1 le_rfl (by omega), (Aux.length_lz77From S 1).symm,
    fun k hk1 hk2 => ?_⟩
  have hlen : k - 1 < (lz77From S 1).length := by
    rw [Aux.length_lz77From]
    omega
  exact Aux.lz77From_getElem? S (k - 1) 1 hlen
