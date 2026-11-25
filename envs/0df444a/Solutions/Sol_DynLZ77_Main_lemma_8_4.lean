-- Prove2me | solution 1 for DynLZ77.Main.lemma_8_4
-- status  : ACCEPTED   (prove)
-- author  : @shaygo
-- created : 2026-11-25T05:08:45.481816+00:00
-- url     : https://prove2.me/submissions/d19f3ff3-273e-431b-9f7b-75229be9231a

import Mathlib.Data.List.PeriodicityLemma
import Theorems.Thm_DynLZ77_KK_local_sparse
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

/-! ## Periods of fragments, Equation (1) of Kempa–Kociumaka, and the construction -/

namespace DynLZ77.Main.Aux

section Periods

variable {α : Type}

theorem sub_eq_window (T : List α) {a len : ℕ} (ha : 1 ≤ a) (hlen : 1 ≤ len) :
    sub T a (a + len - 1) = (T.drop (a - 1)).take len := by
  unfold sub
  congr 1
  omega

theorem window_window (T : List α) {a L e t : ℕ} (h : e + t ≤ L) :
    (((T.drop a).take L).drop e).take t = (T.drop (a + e)).take t := by
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]

theorem getElem?_window (W : List α) {e k t : ℕ} (hk : k < t) :
    ((W.drop e).take t)[k]? = W[e + k]? := by
  rw [List.getElem?_take, if_pos hk, List.getElem?_drop]

/-- The mission's `IsPeriod` (1-based) is Mathlib's `List.HasPeriod` with `p ≥ 1`. -/
theorem isPeriod_iff_hasPeriod (w : List α) (p : ℕ) : IsPeriod w p ↔ 1 ≤ p ∧ w.HasPeriod p := by
  rw [List.hasPeriod_iff_getElem?]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun j hj => ?_⟩
    have h' := h (j + 1) (by omega) (by omega)
    rwa [show j + 1 - 1 = j by omega, show j + 1 + p - 1 = j + p by omega] at h'
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun i hi1 hip => ?_⟩
    have h' := h (i - 1) (by omega)
    rwa [show i - 1 + p = i + p - 1 by omega] at h'

theorem per_isPeriod (w : List α) : IsPeriod w (per w) := by
  classical
  unfold per
  exact Nat.find_spec _

theorem per_le_of_isPeriod {w : List α} {p : ℕ} (h : IsPeriod w p) : per w ≤ p := by
  classical
  unfold per
  exact Nat.find_min' _ h

theorem three_mul_le_of_real {q τ : ℕ} (h : (q : ℝ) ≤ (τ : ℝ) / 3) : 3 * q ≤ τ := by
  have h' : (q : ℝ) * 3 ≤ τ := (le_div_iff₀ three_pos).1 h
  have h'' : q * 3 ≤ τ := by exact_mod_cast h'
  omega

/-- Gluing: if the first `τ` letters of `W` have period `p` and every length-`τ` window of `W` has
some period `q` with `3q ≤ τ` (and `3p ≤ τ`), then `W` has period `p`. Each new letter is reached
through the overlap of its window with the part already known, where Fine–Wilf applies. -/
theorem hasPeriod_of_windows {W : List α} {τ p : ℕ} (hτ : τ ≤ W.length) (hp1 : 1 ≤ p)
    (hp3 : 3 * p ≤ τ) (h0 : (W.take τ).HasPeriod p)
    (hwin : ∀ e, e + τ ≤ W.length → ∃ q, 1 ≤ q ∧ 3 * q ≤ τ ∧ ((W.drop e).take τ).HasPeriod q) :
    W.HasPeriod p := by
  have key : ∀ m, τ ≤ m → m ≤ W.length → (W.take m).HasPeriod p := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => intro _; exact h0
    | succ m hm ih =>
      intro hmL
      have ih' := List.hasPeriod_iff_getElem?.1 (ih (by omega))
      rw [List.length_take, Nat.min_eq_left (by omega)] at ih'
      rw [List.hasPeriod_iff_getElem?, List.length_take, Nat.min_eq_left hmL]
      intro j hj
      rw [List.getElem?_take, List.getElem?_take, if_pos (by omega), if_pos (by omega)]
      by_cases hjm : j + p < m
      · have h' := ih' j (by omega)
        rwa [List.getElem?_take, List.getElem?_take, if_pos (by omega), if_pos hjm] at h'
      · -- the new letter `W[m]`, compared with `W[m - p]` inside the window ending at `m`
        have hjm' : j + p = m := by omega
        obtain ⟨q, hq1, hq3, hX⟩ := hwin (m + 1 - τ) (by omega)
        have hXlen : ((W.drop (m + 1 - τ)).take τ).length = τ := by
          rw [List.length_take, List.length_drop]
          omega
        have hOX : (W.drop (m + 1 - τ)).take (τ - 1) =
            ((W.drop (m + 1 - τ)).take τ).take (τ - 1) := by
          rw [List.take_take, Nat.min_eq_left (by omega)]
        have hOlen : ((W.drop (m + 1 - τ)).take (τ - 1)).length = τ - 1 := by
          rw [List.length_take, List.length_drop]
          omega
        have hO_q : ((W.drop (m + 1 - τ)).take (τ - 1)).HasPeriod q := by
          rw [hOX]
          exact hX.infix (List.take_prefix _ _).isInfix
        have hO_p : ((W.drop (m + 1 - τ)).take (τ - 1)).HasPeriod p := by
          rw [List.hasPeriod_iff_getElem?, hOlen]
          intro k hk
          rw [getElem?_window W (by omega), getElem?_window W (by omega)]
          have h' := ih' (m + 1 - τ + k) (by omega)
          rwa [List.getElem?_take, List.getElem?_take, if_pos (by omega), if_pos (by omega),
            show m + 1 - τ + k + p = m + 1 - τ + (k + p) by omega] at h'
        have hgpos : 1 ≤ Nat.gcd p q := Nat.gcd_pos_of_pos_left q hp1
        have hg := hO_p.gcd hO_q (by rw [hOlen]; omega)
        have hmod : ∀ r, r ≤ τ - 1 → Nat.gcd p q ∣ r →
            (τ - 1 - r) % Nat.gcd p q = (τ - 1) % Nat.gcd p q := by
          intro r hr hgr
          obtain ⟨c, rfl⟩ := hgr
          conv_rhs => rw [show τ - 1 = (τ - 1 - Nat.gcd p q * c) + Nat.gcd p q * c by omega]
          rw [Nat.add_mul_mod_self_left]
        have hXq := List.hasPeriod_iff_getElem?.1 hX (τ - 1 - q) (by rw [hXlen]; omega)
        rw [show τ - 1 - q + q = τ - 1 by omega] at hXq
        have h1 := hg.getElem?_mod _ (τ - 1 - p) _ (by rw [hOlen]; omega)
        have h2 := hg.getElem?_mod _ (τ - 1 - q) _ (by rw [hOlen]; omega)
        rw [hmod p (by omega) (Nat.gcd_dvd_left p q)] at h1
        rw [hmod q (by omega) (Nat.gcd_dvd_right p q)] at h2
        -- `O[τ-1-p] = O[(τ-1) mod g] = O[τ-1-q]`, and `X[τ-1-q] = X[τ-1]` by the period `q`
        have hOpq : ((W.drop (m + 1 - τ)).take (τ - 1))[τ - 1 - p]? =
            ((W.drop (m + 1 - τ)).take (τ - 1))[τ - 1 - q]? := h1.symm.trans h2
        rw [getElem?_window W (by omega), getElem?_window W (by omega)] at hOpq
        rw [getElem?_window W (by omega), getElem?_window W (by omega)] at hXq
        rw [show j + p = m + 1 - τ + (τ - 1) by omega, show j = m + 1 - τ + (τ - 1 - p) by omega]
        exact hOpq.trans hXq
  have h := key W.length hτ le_rfl
  rwa [List.take_length] at h

/-- **Equation (1)** of [KK19]: if every length-`τ` fragment starting in `[i..i+2τ)` has period at
most `τ/3`, then so does `T[i..i+3τ−2]`. -/
theorem per_le_of_all_frags (T : List α) {i τ : ℕ} (hi : 1 ≤ i) (hτ : 1 ≤ τ)
    (hn : i + 3 * τ - 2 ≤ T.length)
    (hQ : ∀ y, i ≤ y → y < i + 2 * τ → ((per (sub T y (y + τ - 1)) : ℝ) ≤ (τ : ℝ) / 3)) :
    ((per (sub T i (i + 3 * τ - 2)) : ℝ) ≤ (τ : ℝ) / 3) := by
  have hW : sub T i (i + 3 * τ - 2) = (T.drop (i - 1)).take (3 * τ - 1) := by
    rw [show i + 3 * τ - 2 = i + (3 * τ - 1) - 1 by omega]
    exact sub_eq_window T hi (by omega)
  have hWlen : ((T.drop (i - 1)).take (3 * τ - 1)).length = 3 * τ - 1 := by
    rw [List.length_take, List.length_drop]
    omega
  have hfrag : ∀ e, e + τ ≤ 3 * τ - 1 →
      sub T (i + e) (i + e + τ - 1) = (((T.drop (i - 1)).take (3 * τ - 1)).drop e).take τ := by
    intro e he
    rw [window_window T he, sub_eq_window T (a := i + e) (len := τ) (by omega) hτ,
      show i + e - 1 = i - 1 + e by omega]
  have hq : ∀ e, e + τ ≤ 3 * τ - 1 → ∃ q, 1 ≤ q ∧ 3 * q ≤ τ ∧
      ((((T.drop (i - 1)).take (3 * τ - 1)).drop e).take τ).HasPeriod q := by
    intro e he
    refine ⟨per (sub T (i + e) (i + e + τ - 1)), (per_isPeriod _).1,
      three_mul_le_of_real (hQ (i + e) (by omega) (by omega)), ?_⟩
    rw [← hfrag e he]
    exact ((isPeriod_iff_hasPeriod _ _).1 (per_isPeriod _)).2
  obtain ⟨p, hp1, hp3, hp⟩ := hq 0 (by omega)
  rw [List.drop_zero] at hp
  have hper : ((T.drop (i - 1)).take (3 * τ - 1)).HasPeriod p :=
    hasPeriod_of_windows (by rw [hWlen]; omega) hp1 hp3 hp
      (fun e he => hq e (by rw [hWlen] at he; exact he))
  have hle : per (sub T i (i + 3 * τ - 2)) ≤ p := by
    rw [hW]
    exact per_le_of_isPeriod ((isPeriod_iff_hasPeriod _ _).2 ⟨hp1, hper⟩)
  rw [le_div_iff₀ three_pos]
  exact_mod_cast (by omega : per (sub T i (i + 3 * τ - 2)) * 3 ≤ τ)

/-- A length-`τ` fragment starting in `[i..i+2τ)` has period at most that of `T[i..i+3τ−2]`. -/
theorem per_frag_le (T : List α) {i τ y : ℕ} (hi : 1 ≤ i) (hτ : 1 ≤ τ)
    (hiy : i ≤ y) (hy : y < i + 2 * τ) :
    per (sub T y (y + τ - 1)) ≤ per (sub T i (i + 3 * τ - 2)) := by
  apply per_le_of_isPeriod
  have hW : sub T i (i + 3 * τ - 2) = (T.drop (i - 1)).take (3 * τ - 1) := by
    rw [show i + 3 * τ - 2 = i + (3 * τ - 1) - 1 by omega]
    exact sub_eq_window T hi (by omega)
  have hfr : sub T y (y + τ - 1) = (((T.drop (i - 1)).take (3 * τ - 1)).drop (y - i)).take τ := by
    rw [window_window T (by omega), sub_eq_window T (a := y) (len := τ) (by omega) hτ,
      show i - 1 + (y - i) = y - 1 by omega]
  obtain ⟨h1, hP⟩ := (isPeriod_iff_hasPeriod _ _).1 (per_isPeriod (sub T i (i + 3 * τ - 2)))
  have hP' : ((T.drop (i - 1)).take (3 * τ - 1)).HasPeriod (per (sub T i (i + 3 * τ - 2))) := by
    rw [← hW]
    exact hP
  rw [isPeriod_iff_hasPeriod, hfr]
  exact ⟨h1, hP'.infix ((List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix)⟩

open DynLZ77.KK in
/-- Membership in Construction 8.1 depends only on the length-`τ` fragments at offsets `0..τ`. -/
theorem sync_transfer (T : List α) (τ : ℕ) (f : List α → ℕ) {i j : ℕ}
    (hfr : ∀ d ≤ τ, sub T (i + d) (i + d + τ - 1) = sub T (j + d) (j + d + τ - 1))
    (hj : 1 ≤ j ∧ j ≤ T.length + 1 - 2 * τ) (hi : i ∈ syncSet T τ f) : j ∈ syncSet T τ f := by
  classical
  unfold syncSet at hi ⊢
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨Finset.mem_Icc.2 hj, ?_⟩
  have hQ : ∀ d ≤ τ, (InQ T τ (i + d) ↔ InQ T τ (j + d)) := fun d hd => by
    unfold InQ
    rw [hfr d hd]
  have h0 : sub T i (i + τ - 1) = sub T j (j + τ - 1) := hfr 0 (Nat.zero_le _)
  have hτ' : sub T (i + τ) (i + 2 * τ - 1) = sub T (j + τ) (j + 2 * τ - 1) := by
    have h' := hfr τ le_rfl
    rwa [show i + τ + τ - 1 = i + 2 * τ - 1 by omega,
      show j + τ + τ - 1 = j + 2 * τ - 1 by omega] at h'
  have hall : ∀ (P : List α → Prop),
      (∀ k ∈ Finset.Icc i (i + τ), ¬ InQ T τ k → P (sub T k (k + τ - 1))) →
      ∀ k ∈ Finset.Icc j (j + τ), ¬ InQ T τ k → P (sub T k (k + τ - 1)) := by
    intro P h k hk hnq
    rw [Finset.mem_Icc] at hk
    have hd : k - j ≤ τ := by omega
    have e1 : k = j + (k - j) := by omega
    have h' := h (i + (k - j)) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
      (fun hq => hnq (by rw [e1]; exact (hQ _ hd).1 hq))
    rwa [hfr _ hd, ← e1] at h'
  rcases hi.2 with ⟨hnq, hmin⟩ | ⟨hnq, hmin⟩
  · left
    refine ⟨fun hq => hnq ((hQ 0 (Nat.zero_le _)).2 hq), ?_⟩
    rw [← h0]
    exact hall (fun s => f (sub T i (i + τ - 1)) ≤ f s) hmin
  · right
    refine ⟨fun hq => hnq ((hQ τ le_rfl).2 hq), ?_⟩
    rw [← hτ']
    exact hall (fun s => f (sub T (i + τ) (i + 2 * τ - 1)) ≤ f s) hmin

end Periods

end DynLZ77.Main.Aux

open DynLZ77.Main DynLZ77.KK

/-- **Lemma 8.4** (p. 48), reduced to the localized size bound for Construction 8.1 of [KK19]
(`DynLZ77.KK.local_sparse`): Construction 8.1, restricted to the `11τ`-neighbourhood of `I`, is an
`I`-local `τ`-synchronizing set for every identifier (Lemma 8.2 of [KK19], with Equation (1)
proved by Fine–Wilf), and the child lemma supplies an identifier making it small. -/
theorem solution : ∃ C : ℝ, ∀ {α : Type} [DecidableEq α] (T : List α) (I : Finset ℕ) (τ : ℕ),
    I ⊆ Finset.Icc 1 T.length → 1 ≤ τ → τ ≤ T.length / 2 →
      ∃ Sy : Finset ℕ, IsLocalSyncSet T I τ Sy ∧ (Sy.card : ℝ) ≤ C * (I.card : ℝ) := by
  obtain ⟨C, hC⟩ := DynLZ77.KK.local_sparse
  refine ⟨C, fun {α} _ T I τ hI hτ1 hτn => ?_⟩
  obtain ⟨f, hf⟩ := hC T I τ hI hτ1 hτn
  refine ⟨(syncSet T τ f).filter (fun x => ∃ i ∈ I, i ≤ x + 11 * τ ∧ x ≤ i + 11 * τ),
    ⟨?_, ?_⟩, hf⟩
  · -- consistency
    have hclose : ∀ x, x ∈ close τ I → ∃ k ∈ I, k ≤ x + 10 * τ ∧ x ≤ k + 10 * τ := by
      intro x hx
      unfold close at hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨k, hk, hxk⟩ := hx
      rw [Finset.mem_Icc] at hxk
      exact ⟨k, hk, by omega, by omega⟩
    intro i hi j hj hsub
    rw [Finset.mem_inter, Finset.mem_Icc] at hi hj
    have hwi : sub T i (i + 2 * τ - 1) = (T.drop (i - 1)).take (2 * τ) :=
      Aux.sub_eq_window T hi.2.1 (by omega)
    have hwj : sub T j (j + 2 * τ - 1) = (T.drop (j - 1)).take (2 * τ) :=
      Aux.sub_eq_window T hj.2.1 (by omega)
    have hfr : ∀ d ≤ τ, sub T (i + d) (i + d + τ - 1) = sub T (j + d) (j + d + τ - 1) := by
      intro d hd
      have e1 : sub T (i + d) (i + d + τ - 1) = ((sub T i (i + 2 * τ - 1)).drop d).take τ := by
        rw [Aux.sub_eq_window T (a := i + d) (len := τ) (by omega) hτ1, hwi,
          Aux.window_window T (a := i - 1) (L := 2 * τ) (e := d) (t := τ) (by omega),
          show i + d - 1 = i - 1 + d by omega]
      have e2 : sub T (j + d) (j + d + τ - 1) = ((sub T j (j + 2 * τ - 1)).drop d).take τ := by
        rw [Aux.sub_eq_window T (a := j + d) (len := τ) (by omega) hτ1, hwj,
          Aux.window_window T (a := j - 1) (L := 2 * τ) (e := d) (t := τ) (by omega),
          show j + d - 1 = j - 1 + d by omega]
      rw [e1, e2, hsub]
    rw [Finset.mem_filter, Finset.mem_filter]
    have hri : ∃ k ∈ I, k ≤ i + 11 * τ ∧ i ≤ k + 11 * τ := by
      obtain ⟨k, hk, h1, h2⟩ := hclose i hi.1
      exact ⟨k, hk, by omega, by omega⟩
    have hrj : ∃ k ∈ I, k ≤ j + 11 * τ ∧ j ≤ k + 11 * τ := by
      obtain ⟨k, hk, h1, h2⟩ := hclose j hj.1
      exact ⟨k, hk, by omega, by omega⟩
    constructor
    · rintro ⟨hs, _⟩
      exact ⟨Aux.sync_transfer T τ f hfr ⟨hj.2.1, hj.2.2⟩ hs, hrj⟩
    · rintro ⟨hs, _⟩
      exact ⟨Aux.sync_transfer T τ f (fun d hd => (hfr d hd).symm) ⟨hi.2.1, hi.2.2⟩ hs, hri⟩
  · -- density
    intro i hi
    rw [Finset.mem_inter, Finset.mem_Icc] at hi
    obtain ⟨hic, hi1, hi2⟩ := hi
    have hn : i + 3 * τ - 2 ≤ T.length := by omega
    obtain ⟨k₀, hk₀, hk₀1, hk₀2⟩ : ∃ k ∈ I, k ≤ i + 10 * τ ∧ i ≤ k + 10 * τ := by
      unfold close at hic
      rw [Finset.mem_biUnion] at hic
      obtain ⟨k, hk, hxk⟩ := hic
      rw [Finset.mem_Icc] at hxk
      exact ⟨k, hk, by omega, by omega⟩
    constructor
    · -- no element in `[i..i+τ)` ⇒ the window is periodic
      intro hnone
      by_contra hP
      have hex : ∃ y, i ≤ y ∧ y < i + 2 * τ ∧ ¬ InQ T τ y := by
        by_contra hall
        apply hP
        apply Aux.per_le_of_all_frags T hi1 hτ1 hn
        intro y h1 h2
        by_contra hq
        exact hall ⟨y, h1, h2, hq⟩
      classical
      obtain ⟨y, hyF, hmin⟩ := Finset.exists_min_image
        ((Finset.Ico i (i + 2 * τ)).filter (fun y => ¬ InQ T τ y))
        (fun y => f (sub T y (y + τ - 1)))
        (by
          obtain ⟨y, h1, h2, h3⟩ := hex
          exact ⟨y, Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨h1, h2⟩, h3⟩⟩)
      rw [Finset.mem_filter, Finset.mem_Ico] at hyF
      obtain ⟨⟨hy1, hy2⟩, hyQ⟩ := hyF
      have hmin' : ∀ k, i ≤ k → k < i + 2 * τ → ¬ InQ T τ k →
          f (sub T y (y + τ - 1)) ≤ f (sub T k (k + τ - 1)) :=
        fun k h1 h2 h3 => hmin k (Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨h1, h2⟩, h3⟩)
      by_cases hyl : y < i + τ
      · apply hnone y (Finset.mem_Ico.2 ⟨hy1, hyl⟩)
        refine Finset.mem_filter.2 ⟨?_, ⟨k₀, hk₀, by omega, by omega⟩⟩
        unfold syncSet
        refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩, Or.inl ⟨hyQ, ?_⟩⟩
        intro k hk hkQ
        rw [Finset.mem_Icc] at hk
        exact hmin' k (by omega) (by omega) hkQ
      · apply hnone (y - τ) (Finset.mem_Ico.2 ⟨by omega, by omega⟩)
        refine Finset.mem_filter.2 ⟨?_, ⟨k₀, hk₀, by omega, by omega⟩⟩
        unfold syncSet
        have e1 : y - τ + τ = y := by omega
        have e2 : y - τ + 2 * τ - 1 = y + τ - 1 := by omega
        refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨by omega, by omega⟩,
          Or.inr ⟨by rw [e1]; exact hyQ, ?_⟩⟩
        intro k hk hkQ
        rw [Finset.mem_Icc] at hk
        rw [e1, e2]
        exact hmin' k (by omega) (by omega) hkQ
    · -- periodic window ⇒ every fragment in `[i..i+2τ)` is periodic ⇒ no element in `[i..i+τ)`
      intro hP x hx hxS
      classical
      rw [Finset.mem_Ico] at hx
      rw [Finset.mem_filter] at hxS
      have hS := hxS.1
      unfold syncSet at hS
      rw [Finset.mem_filter] at hS
      have hQy : ∀ y, i ≤ y → y < i + 2 * τ → InQ T τ y := by
        intro y h1 h2
        unfold InQ
        have h' := Aux.per_frag_le T hi1 hτ1 h1 h2
        exact le_trans (by exact_mod_cast h') hP
      rcases hS.2 with ⟨hq, _⟩ | ⟨hq, _⟩
      · exact hq (hQy x (by omega) (by omega))
      · exact hq (hQy (x + τ) (by omega) (by omega))
