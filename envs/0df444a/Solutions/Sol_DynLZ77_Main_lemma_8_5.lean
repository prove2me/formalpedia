-- Prove2me | solution 1 for DynLZ77.Main.lemma_8_5
-- status  : ACCEPTED   (prove)
-- author  : @shaygo
-- created : 2026-11-25T20:52:16.1745+00:00
-- url     : https://prove2.me/submissions/918c9ed7-bd2e-4aac-b610-0bc0a66d0e89

import Mathlib.Data.List.PeriodicityLemma
import Mathlib.Data.List.Rotate
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_DynLZ77_KK_SyncConstruction
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


/-!
# Runs, canonical rotations and Lyndon-type positions
-/

namespace DynLZ77.Main.Aux

section Runs

variable {α : Type}

/-- `S` has period `p` on the positions `[a..b]` (1-based). -/
def PerOn (S : List α) (a b p : ℕ) : Prop :=
  ∀ j, a ≤ j → j + p ≤ b → S[j - 1]? = S[j + p - 1]?

theorem PerOn.mono {S : List α} {a b p a' b' : ℕ} (h : PerOn S a b p) (ha : a ≤ a')
    (hb : b' ≤ b) : PerOn S a' b' p :=
  fun j hj hjb => h j (by omega) (by omega)

theorem getElem?_sub (S : List α) {a b k : ℕ} (hk : k < b + 1 - a) :
    (sub S a b)[k]? = S[a - 1 + k]? := by
  unfold sub
  rw [List.getElem?_take, if_pos hk, List.getElem?_drop]

theorem getElem?_sub_none (S : List α) {a b k : ℕ} (hk : b + 1 - a ≤ k) :
    (sub S a b)[k]? = none := by
  apply List.getElem?_eq_none
  unfold sub
  rw [List.length_take]
  omega

theorem length_sub (S : List α) {a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ S.length) :
    (sub S a b).length = b + 1 - a := by
  unfold sub
  rw [List.length_take, List.length_drop]
  omega

/-- A substring of a substring. -/
theorem sub_of_sub (S : List α) {a b c d : ℕ} (ha : 1 ≤ a) (hc : 1 ≤ c) (hcd : c ≤ d + 1)
    (hd : d ≤ b + 1 - a) : sub (sub S a b) c d = sub S (a + c - 1) (a + d - 1) := by
  unfold sub
  rw [window_window S (by omega), show a + c - 1 - 1 = a - 1 + (c - 1) by omega,
    show a + d - 1 + 1 - (a + c - 1) = d + 1 - c by omega]

theorem isPeriod_sub_iff (S : List α) {a b p : ℕ} (ha : 1 ≤ a) (hb : b ≤ S.length) :
    IsPeriod (sub S a b) p ↔ 1 ≤ p ∧ PerOn S a b p := by
  unfold IsPeriod PerOn
  rw [length_sub S ha hb]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun j hj hjb => ?_⟩
    have h' := h (j + 1 - a) (by omega) (by omega)
    rw [getElem?_sub S (k := j + 1 - a - 1) (by omega),
      getElem?_sub S (k := j + 1 - a + p - 1) (by omega)] at h'
    rw [show a - 1 + (j + 1 - a - 1) = j - 1 by omega,
      show a - 1 + (j + 1 - a + p - 1) = j + p - 1 by omega] at h'
    exact h'
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun t ht htb => ?_⟩
    rw [getElem?_sub S (k := t - 1) (by omega), getElem?_sub S (k := t + p - 1) (by omega)]
    have h' := h (a + t - 1) (by omega) (by omega)
    rw [show a + t - 1 - 1 = a - 1 + (t - 1) by omega,
      show a + t - 1 + p - 1 = a - 1 + (t + p - 1) by omega] at h'
    exact h'

theorem one_le_per (w : List α) : 1 ≤ per w := (per_isPeriod w).1

theorem perOn_per (S : List α) {a b : ℕ} (ha : 1 ≤ a) (hb : b ≤ S.length) :
    PerOn S a b (per (sub S a b)) :=
  ((isPeriod_sub_iff S ha hb).1 (per_isPeriod _)).2

theorem per_sub_le (S : List α) {a b p : ℕ} (ha : 1 ≤ a) (hb : b ≤ S.length) (hp : 1 ≤ p)
    (h : PerOn S a b p) : per (sub S a b) ≤ p :=
  per_le_of_isPeriod ((isPeriod_sub_iff S ha hb).2 ⟨hp, h⟩)

/-- Two windows at distance `p` inside a stretch with period `p` are equal. -/
theorem sub_shift (S : List α) {a b p x len : ℕ} (h : PerOn S a b p) (hx : a ≤ x) (hx1 : 1 ≤ x)
    (hlen : x + p + len - 1 ≤ b) (hb : b ≤ S.length) :
    sub S x (x + len - 1) = sub S (x + p) (x + p + len - 1) := by
  apply List.ext_getElem?
  intro t
  by_cases ht : t < len
  · rw [getElem?_sub S (k := t) (by omega), getElem?_sub S (k := t) (by omega)]
    have := h (x + t) (by omega) (by omega)
    rw [show x - 1 + t = x + t - 1 by omega, show x + p - 1 + t = x + t + p - 1 by omega]
    exact this
  · rw [getElem?_sub_none S (by omega), getElem?_sub_none S (by omega)]

/-- **Fine–Wilf** for `PerOn`. -/
theorem perOn_gcd (S : List α) {x y p q : ℕ} (hx : 1 ≤ x) (hy : y ≤ S.length) (hp : 1 ≤ p)
    (hq : 1 ≤ q) (hP : PerOn S x y p) (hQ : PerOn S x y q) (hlen : p + q ≤ y + 1 - x) :
    PerOn S x y (Nat.gcd p q) := by
  have hP' := (isPeriod_iff_hasPeriod _ _).1 ((isPeriod_sub_iff S hx hy).2 ⟨hp, hP⟩)
  have hQ' := (isPeriod_iff_hasPeriod _ _).1 ((isPeriod_sub_iff S hx hy).2 ⟨hq, hQ⟩)
  have hg := hP'.2.gcd hQ'.2 (by rw [length_sub S hx hy]; omega)
  exact ((isPeriod_sub_iff S hx hy).1
    ((isPeriod_iff_hasPeriod _ _).2 ⟨Nat.gcd_pos_of_pos_left _ hp, hg⟩)).2

/-- A period `g` on a window of length `≥ p + g` inside a stretch with period `p` extends to the
whole stretch. -/
theorem perOn_extend (S : List α) {a b c d p g : ℕ} (hP : PerOn S a b p) (hG : PerOn S c d g)
    (hp : 1 ≤ p) (hac : a ≤ c) (hdb : d ≤ b) (hlen : p + g ≤ d + 1 - c) : PerOn S a b g := by
  -- extend to the right
  have hright : ∀ m, d + m ≤ b → PerOn S c (d + m) g := by
    intro m
    induction m with
    | zero => intro _; simpa using hG
    | succ m ih =>
      intro hm j hj hjb
      by_cases hjm : j + g ≤ d + m
      · exact ih (by omega) j hj hjm
      · have e1 := hP (j - p) (by omega) (by omega)
        have e2 := ih (by omega) (j - p) (by omega) (by omega)
        have e3 := hP (j - p + g) (by omega) (by omega)
        rw [show j - p + p - 1 = j - 1 by omega] at e1
        rw [show j - p + g + p - 1 = j + g - 1 by omega] at e3
        rw [← e1, e2, e3]
  have hcb : PerOn S c b g := by
    have := hright (b - d) (by omega)
    rwa [show d + (b - d) = b by omega] at this
  -- extend to the left
  have hleft : ∀ m, m ≤ c - a → PerOn S (c - m) b g := by
    intro m
    induction m with
    | zero => intro _; simpa using hcb
    | succ m ih =>
      intro hm j hj hjb
      by_cases hjm : c - m ≤ j
      · exact ih (by omega) j hjm hjb
      · have e1 := hP j (by omega) (by omega)
        have e2 := ih (by omega) (j + p) (by omega) (by omega)
        have e3 := hP (j + g) (by omega) (by omega)
        rw [show j + p + g - 1 = j + g + p - 1 by omega] at e2
        rw [e1, e2, ← e3]
  have := hleft (c - a) le_rfl
  rwa [show c - (c - a) = a by omega] at this

/-- The window of length `p` one step further is the rotation by one. -/
theorem sub_succ_rotate (S : List α) {a b p x : ℕ} (h : PerOn S a b p) (hp : 1 ≤ p)
    (hx : a ≤ x) (hx1 : 1 ≤ x) (hxb : x + p ≤ b) (hb : b ≤ S.length) :
    sub S (x + 1) (x + 1 + p - 1) = (sub S x (x + p - 1)).rotate 1 := by
  apply List.ext_getElem?
  intro t
  have hlen : (sub S x (x + p - 1)).length = p := by rw [length_sub S hx1 (by omega)]; omega
  by_cases ht : t < p
  · rw [List.getElem?_rotate (by rw [hlen]; exact ht), hlen, getElem?_sub S (k := t) (by omega)]
    rcases Nat.lt_or_ge (t + 1) p with h1 | h1
    · rw [Nat.mod_eq_of_lt h1, getElem?_sub S (k := t + 1) (by omega)]
      congr 1
      omega
    · have h2 : t + 1 = p := by omega
      rw [h2, Nat.mod_self, getElem?_sub S (k := 0) (by omega)]
      have := h x hx hxb
      rw [show x + 1 - 1 + t = x + p - 1 by omega, ← this, show x - 1 + 0 = x - 1 by omega]
  · rw [getElem?_sub_none S (by omega), List.getElem?_eq_none (by rw [List.length_rotate, hlen]; omega)]

theorem sub_add_rotate (S : List α) {a b p : ℕ} (h : PerOn S a b p) (hp : 1 ≤ p) (ha : 1 ≤ a)
    (hb : b ≤ S.length) : ∀ m, a + m + p - 1 ≤ b →
      sub S (a + m) (a + m + p - 1) = (sub S a (a + p - 1)).rotate m
  | 0, _ => by simp
  | m + 1, hm => by
      rw [show a + (m + 1) = a + m + 1 by omega,
        sub_succ_rotate S h hp (by omega) (by omega) (by omega) hb,
        sub_add_rotate S h hp ha hb m (by omega), List.rotate_rotate]

/-- A canonical representative of the rotation class of `P` (any fixed choice; the proof only
needs that rotated lists get the same representative). -/
noncomputable def canon (P : List α) : List α := Classical.epsilon (fun Q => List.IsRotated Q P)

theorem canon_isRotated (P : List α) : List.IsRotated (canon P) P :=
  Classical.epsilon_spec (p := fun Q => List.IsRotated Q P) ⟨P, List.IsRotated.refl P⟩

theorem canon_eq {P P' : List α} (h : List.IsRotated P P') : canon P = canon P' := by
  unfold canon
  congr 1
  funext Q
  exact propext ⟨fun hQ => hQ.trans h, fun hQ => hQ.trans h.symm⟩

open Classical in
/-- The first position `x ∈ [a..a+p)` of the run `S[a..b]` (`p = per(S[a..b])`) whose `p`-window
is the canonical rotation of the run's root `S[a..a+p)`. -/
noncomputable def lynStart (S : List α) (a b : ℕ) : ℕ :=
  if h : ∃ x, a ≤ x ∧ x < a + per (sub S a b) ∧
      sub S x (x + per (sub S a b) - 1) = canon (sub S a (a + per (sub S a b) - 1))
  then Nat.find h else 0

/-- The two leftmost positions of the run `S[a..b]` whose `p`-window is the canonical rotation
(the paper's `Lyn_R`). -/
noncomputable def lynPos (S : List α) (a b : ℕ) : Finset ℕ :=
  {lynStart S a b, lynStart S a b + per (sub S a b)}

theorem card_lynPos_le (S : List α) (a b : ℕ) : (lynPos S a b).card ≤ 2 := by
  unfold lynPos
  exact (Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton])

theorem lynStart_spec (S : List α) {a b p : ℕ} (ha : 1 ≤ a) (hb : b ≤ S.length)
    (hp : per (sub S a b) = p) (h2p : 2 * p ≤ b + 1 - a) :
    a ≤ lynStart S a b ∧ lynStart S a b < a + p ∧
      sub S (lynStart S a b) (lynStart S a b + p - 1) = canon (sub S a (a + p - 1)) := by
  have hp1 : 1 ≤ p := by rw [← hp]; exact one_le_per _
  have hrun : PerOn S a b p := by rw [← hp]; exact perOn_per S ha hb
  have hex : ∃ x, a ≤ x ∧ x < a + p ∧ sub S x (x + p - 1) = canon (sub S a (a + p - 1)) := by
    obtain ⟨n, hn⟩ := (canon_isRotated (sub S a (a + p - 1))).symm
    have hlen : (sub S a (a + p - 1)).length = p := by rw [length_sub S ha (by omega)]; omega
    have hmod := Nat.mod_lt n hp1
    refine ⟨a + n % p, by omega, by omega, ?_⟩
    rw [sub_add_rotate S hrun hp1 ha hb (n % p) (by omega), ← hn]
    have hm := List.rotate_mod (sub S a (a + p - 1)) n
    rw [hlen] at hm
    exact hm
  classical
  unfold lynStart
  rw [hp, dif_pos hex]
  exact Nat.find_spec hex

/-- No two equal `p`-windows start within distance `< p` in a run with smallest period `p`. -/
theorem window_inj (S : List α) {a b p x y : ℕ} (ha : 1 ≤ a) (hb : b ≤ S.length)
    (hp : per (sub S a b) = p) (h2p : 2 * p ≤ b + 1 - a) (hax : a ≤ x) (hxy : x < y)
    (hy : y < a + p) (heq : sub S x (x + p - 1) = sub S y (y + p - 1)) : False := by
  have hp1 : 1 ≤ p := by rw [← hp]; exact one_le_per _
  have hrun : PerOn S a b p := by rw [← hp]; exact perOn_per S ha hb
  have hd : PerOn S x (y + p - 1) (y - x) := by
    intro j hj hjb
    have h1 : (sub S x (x + p - 1))[j - x]? = (sub S y (y + p - 1))[j - x]? := by rw [heq]
    rw [getElem?_sub S (k := j - x) (by omega), getElem?_sub S (k := j - x) (by omega)] at h1
    rw [show j - 1 = x - 1 + (j - x) by omega, h1]
    congr 1
    omega
  have hg := perOn_gcd S (show 1 ≤ x by omega) (show y + p - 1 ≤ S.length by omega)
    (show 1 ≤ y - x by omega) hp1 hd (hrun.mono hax (by omega)) (by omega)
  have hgd : Nat.gcd (y - x) p ≤ y - x := Nat.gcd_le_left _ (by omega)
  have hext := perOn_extend S hrun hg hp1 hax (show y + p - 1 ≤ b by omega) (by omega)
  have hle := per_sub_le S ha hb (Nat.gcd_pos_of_pos_left _ (show 0 < y - x by omega)) hext
  omega

/-- A position of `[a..a+p)` whose window is the canonical rotation is `lynStart`. -/
theorem eq_lynStart (S : List α) {a b p y : ℕ} (ha : 1 ≤ a) (hb : b ≤ S.length)
    (hp : per (sub S a b) = p) (h2p : 2 * p ≤ b + 1 - a) (hay : a ≤ y) (hy : y < a + p)
    (hW : sub S y (y + p - 1) = canon (sub S a (a + p - 1))) : y = lynStart S a b := by
  obtain ⟨h1, h2, h3⟩ := lynStart_spec S ha hb hp h2p
  rcases lt_trichotomy y (lynStart S a b) with h | h | h
  · exact (window_inj S ha hb hp h2p hay h h2 (hW.trans h3.symm)).elim
  · exact h
  · exact (window_inj S ha hb hp h2p h1 h hy (h3.trans hW.symm)).elim

end Runs

section MaxRun

variable {α : Type} [DecidableEq α]

open Classical in
/-- Every highly periodic substring extends to a run with the same period. -/
theorem exists_run (S : List α) {i ℓ : ℕ} (hi : 1 ≤ i) (hiℓ : i + ℓ - 1 ≤ S.length)
    (hhp : 3 * per (sub S i (i + ℓ - 1)) ≤ ℓ) :
    ∃ a b, IsRun S a b (per (sub S i (i + ℓ - 1))) ∧ a ≤ i ∧ i + ℓ - 1 ≤ b := by
  obtain ⟨p, hp⟩ : ∃ p, p = per (sub S i (i + ℓ - 1)) := ⟨_, rfl⟩
  rw [← hp] at hhp ⊢
  have hp1 : 1 ≤ p := by rw [hp]; exact one_le_per _
  have hE : PerOn S i (i + ℓ - 1) p := by rw [hp]; exact perOn_per S hi hiℓ
  -- extend to the left
  have hexA : ∃ a, 1 ≤ a ∧ a ≤ i ∧ PerOn S a (i + ℓ - 1) p := ⟨i, hi, le_rfl, hE⟩
  obtain ⟨a, ha⟩ : ∃ a, a = Nat.find hexA := ⟨_, rfl⟩
  have haspec : 1 ≤ a ∧ a ≤ i ∧ PerOn S a (i + ℓ - 1) p := by rw [ha]; exact Nat.find_spec hexA
  have hamin : ∀ a', a' < a → ¬ (1 ≤ a' ∧ a' ≤ i ∧ PerOn S a' (i + ℓ - 1) p) := by
    intro a' h
    rw [ha] at h
    exact Nat.find_min hexA h
  obtain ⟨ha1, hai, haE⟩ := haspec
  -- extend to the right
  obtain ⟨b, hb⟩ : ∃ b, b = Nat.findGreatest (fun b => PerOn S a b p) S.length := ⟨_, rfl⟩
  have hb1 : i + ℓ - 1 ≤ b := by
    rw [hb]
    exact Nat.le_findGreatest (P := fun b => PerOn S a b p) hiℓ haE
  have hbn : b ≤ S.length := by rw [hb]; exact Nat.findGreatest_le _
  have hbspec : PerOn S a b p := by
    rw [hb]
    exact Nat.findGreatest_spec (P := fun b => PerOn S a b p) hiℓ haE
  have hbmax : ∀ b', b < b' → b' ≤ S.length → ¬ PerOn S a b' p := by
    intro b' h1 h2
    rw [hb] at h1
    exact Nat.findGreatest_is_greatest (P := fun b => PerOn S a b p) h1 h2
  refine ⟨a, b, ⟨ha1, by omega, hbn, ?_, by omega, ?_, ?_⟩, hai, hb1⟩
  · -- the smallest period of the run is `p`
    apply le_antisymm (per_sub_le S ha1 hbn hp1 hbspec)
    have hq := (perOn_per S ha1 hbn).mono hai hb1
    have := per_sub_le S hi hiℓ (one_le_per _) hq
    rw [← hp] at this
    exact this
  · -- left maximality
    unfold charAt
    by_cases ha2 : a = 1
    · rw [if_pos (by omega : a - 1 = 0), if_neg (by omega : ¬ (a - 1 + p = 0))]
      intro h
      rw [List.getElem?_eq_getElem (show a - 1 + p - 1 < S.length by omega)] at h
      simp at h
    · rw [if_neg (by omega : ¬ (a - 1 = 0)), if_neg (by omega : ¬ (a - 1 + p = 0))]
      have hnot := hamin (a - 1) (by omega)
      intro heq
      apply hnot
      refine ⟨by omega, by omega, fun j hj hjb => ?_⟩
      by_cases hja : a ≤ j
      · exact haE j hja hjb
      · rw [show j = a - 1 by omega]
        exact heq
  · -- right maximality
    unfold charAt
    rw [if_neg (by omega : ¬ (b + 1 = 0)), if_neg (by omega : ¬ (b + 1 - p = 0))]
    by_cases hbn' : b = S.length
    · rw [hbn', show S.length + 1 - 1 = S.length by omega, List.getElem?_eq_none le_rfl]
      intro h
      rw [List.getElem?_eq_getElem (show S.length + 1 - p - 1 < S.length by omega)] at h
      simp at h
    · have hnot := hbmax (b + 1) (by omega) (by omega)
      intro heq
      apply hnot
      intro j hj hjb
      by_cases hjb' : j + p ≤ b
      · exact hbspec j hj hjb'
      · rw [show j = b + 1 - p by omega, show b + 1 - p + p - 1 = b + 1 - 1 by omega]
        exact heq.symm

end MaxRun

end DynLZ77.Main.Aux

/-!
# Lemma 8.5 ([BGS24, Lemma 8]): a position lies in `O(log n)` highly periodic runs
-/

namespace DynLZ77.Main.Aux

section Lemma85

variable {α : Type} [DecidableEq α]

theorem lt_add_of_div_eq {x y d : ℕ} (hd : 0 < d) (h : x / d = y / d) : x < y + d := by
  have h1 := Nat.div_add_mod x d
  have h2 := Nat.div_add_mod y d
  have h3 := Nat.mod_lt x hd
  rw [h] at h1
  generalize d * (y / d) = A at h1 h2
  omega

/-- Two runs sharing a stretch of length at least the sum of their periods coincide (the
Fine–Wilf periodicity lemma plus maximality). -/
theorem run_eq_of_overlap (S : List α) {a1 b1 p1 a2 b2 p2 c d : ℕ} (h1 : IsRun S a1 b1 p1)
    (h2 : IsRun S a2 b2 p2) (hc1 : a1 ≤ c) (hc2 : a2 ≤ c) (hd1 : d ≤ b1) (hd2 : d ≤ b2)
    (hlen : p1 + p2 ≤ d + 1 - c) : a1 = a2 ∧ b1 = b2 := by
  obtain ⟨ha1, hab1, hb1, hper1, h2p1, hl1, hr1⟩ := h1
  obtain ⟨ha2, hab2, hb2, hper2, h2p2, hl2, hr2⟩ := h2
  have hp1 : 1 ≤ p1 := by rw [← hper1]; exact one_le_per _
  have hp2 : 1 ≤ p2 := by rw [← hper2]; exact one_le_per _
  have hrun1 : PerOn S a1 b1 p1 := by rw [← hper1]; exact perOn_per S ha1 hb1
  have hrun2 : PerOn S a2 b2 p2 := by rw [← hper2]; exact perOn_per S ha2 hb2
  have hg := perOn_gcd S (show 1 ≤ c by omega) (show d ≤ S.length by omega) hp1 hp2
    (hrun1.mono hc1 hd1) (hrun2.mono hc2 hd2) hlen
  have hg1 : Nat.gcd p1 p2 ≤ p1 := Nat.gcd_le_left _ (by omega)
  have hg2 : Nat.gcd p1 p2 ≤ p2 := Nat.gcd_le_right _ (by omega)
  have hgpos : 1 ≤ Nat.gcd p1 p2 := Nat.gcd_pos_of_pos_left _ (by omega)
  have he1 := perOn_extend S hrun1 hg hp1 hc1 hd1 (by omega)
  have he2 := perOn_extend S hrun2 hg hp2 hc2 hd2 (by omega)
  have hq1 := per_sub_le S ha1 hb1 hgpos he1
  have hq2 := per_sub_le S ha2 hb2 hgpos he2
  rw [hper1] at hq1
  rw [hper2] at hq2
  have hpp : p1 = p2 := by omega
  subst hpp
  -- equal periods: maximality pins both ends
  have hleft : a1 = a2 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · apply hl2
      unfold charAt
      rw [if_neg (by omega : ¬ (a2 - 1 = 0)), if_neg (by omega : ¬ (a2 - 1 + p1 = 0))]
      have := hrun1 (a2 - 1) (by omega) (by omega)
      exact this
    · apply hl1
      unfold charAt
      rw [if_neg (by omega : ¬ (a1 - 1 = 0)), if_neg (by omega : ¬ (a1 - 1 + p1 = 0))]
      exact hrun2 (a1 - 1) (by omega) (by omega)
  have hright : b1 = b2 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · apply hr1
      unfold charAt
      rw [if_neg (by omega : ¬ (b1 + 1 = 0)), if_neg (by omega : ¬ (b1 + 1 - p1 = 0))]
      have := hrun2 (b1 + 1 - p1) (by omega) (by omega)
      rw [show b1 + 1 - p1 + p1 - 1 = b1 + 1 - 1 by omega] at this
      exact this.symm
    · apply hr2
      unfold charAt
      rw [if_neg (by omega : ¬ (b2 + 1 = 0)), if_neg (by omega : ¬ (b2 + 1 - p1 = 0))]
      have := hrun1 (b2 + 1 - p1) (by omega) (by omega)
      rw [show b2 + 1 - p1 + p1 - 1 = b2 + 1 - 1 by omega] at this
      exact this.symm
  exact ⟨hleft, hright⟩

/-- The key of a highly periodic run `r = S[a..b]` containing `i`: the dyadic scale `m` of its
period `p`, the quarter of `[2^m, 2^{m+1})` containing `p`, and the half-`2^m` block of the start
`s = min(i, b + 1 − 3p)` of a `3p`-window around `i`. -/
noncomputable def runKey (S : List α) (i : ℕ) (r : ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (Nat.log 2 (per (sub S r.1 r.2)),
    4 * (per (sub S r.1 r.2) - 2 ^ Nat.log 2 (per (sub S r.1 r.2))) /
      2 ^ Nat.log 2 (per (sub S r.1 r.2)),
    2 * (i - min i (r.2 + 1 - 3 * per (sub S r.1 r.2))) / 2 ^ Nat.log 2 (per (sub S r.1 r.2)))

open Classical in
/-- **Lemma 8.5**, counting form: at most `48·(⌊log₂ n⌋ + 1)` highly periodic runs contain `i`. -/
theorem card_hpRuns_le (S : List α) (i : ℕ) :
    ((Finset.Icc 1 S.length ×ˢ Finset.Icc 1 S.length).filter (fun r : ℕ × ℕ =>
        IsRun S r.1 r.2 (per (sub S r.1 r.2)) ∧ HighlyPeriodic (sub S r.1 r.2) ∧
          r.1 ≤ i ∧ i ≤ r.2)).card ≤ 48 * (Nat.log 2 S.length + 1) := by
  have hcod : ((Finset.range (Nat.log 2 S.length + 1)) ×ˢ (Finset.range 4 ×ˢ Finset.range 12)).card
      = 48 * (Nat.log 2 S.length + 1) := by
    rw [Finset.card_product, Finset.card_product, Finset.card_range, Finset.card_range,
      Finset.card_range]
    omega
  rw [← hcod]
  -- facts about one run of the set
  have hfacts : ∀ r ∈ (Finset.Icc 1 S.length ×ˢ Finset.Icc 1 S.length).filter (fun r : ℕ × ℕ =>
        IsRun S r.1 r.2 (per (sub S r.1 r.2)) ∧ HighlyPeriodic (sub S r.1 r.2) ∧
          r.1 ≤ i ∧ i ≤ r.2),
      IsRun S r.1 r.2 (per (sub S r.1 r.2)) ∧ 3 * per (sub S r.1 r.2) ≤ r.2 + 1 - r.1 ∧
        r.1 ≤ i ∧ i ≤ r.2 ∧ 2 ^ Nat.log 2 (per (sub S r.1 r.2)) ≤ per (sub S r.1 r.2) ∧
        per (sub S r.1 r.2) < 2 * 2 ^ Nat.log 2 (per (sub S r.1 r.2)) := by
    intro r hr
    rw [Finset.mem_filter] at hr
    obtain ⟨-, hR, hhp, hai, hib⟩ := hr
    have hR0 := hR
    obtain ⟨ha1, -, hbn, -, -, -, -⟩ := hR0
    unfold HighlyPeriodic at hhp
    rw [length_sub S ha1 hbn] at hhp
    have hp0 : per (sub S r.1 r.2) ≠ 0 := by have := one_le_per (sub S r.1 r.2); omega
    refine ⟨hR, hhp, hai, hib, Nat.pow_log_le_self 2 hp0, ?_⟩
    have := Nat.lt_pow_succ_log_self Nat.one_lt_two (per (sub S r.1 r.2))
    rw [pow_succ] at this
    omega
  apply Finset.card_le_card_of_injOn (runKey S i)
  · -- the key lands in the box
    intro r hr
    obtain ⟨hR, h3, hai, hib, hlo, hhi⟩ := hfacts r hr
    obtain ⟨ha1, -, hbn, -, -, -, -⟩ := hR
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_product, Finset.mem_range,
      Finset.mem_range, Finset.mem_range]
    simp only [runKey]
    generalize per (sub S r.1 r.2) = p at *
    generalize hm : Nat.log 2 p = m at *
    have hM : 0 < 2 ^ m := Nat.two_pow_pos m
    generalize 2 ^ m = M at *
    refine ⟨?_, ?_, ?_⟩
    · have : Nat.log 2 p ≤ Nat.log 2 S.length := Nat.log_mono_right (by omega)
      omega
    · rw [Nat.div_lt_iff_lt_mul hM]
      omega
    · rw [Nat.div_lt_iff_lt_mul hM]
      omega
  · -- injectivity
    intro r1 hr1 r2 hr2 hkey
    obtain ⟨hR1, h31, hai1, hib1, hlo1, hhi1⟩ := hfacts r1 hr1
    obtain ⟨hR2, h32, hai2, hib2, hlo2, hhi2⟩ := hfacts r2 hr2
    simp only [runKey, Prod.mk.injEq] at hkey
    obtain ⟨hm, ht, hu⟩ := hkey
    generalize hp1 : per (sub S r1.1 r1.2) = p1 at *
    generalize hp2 : per (sub S r2.1 r2.2) = p2 at *
    generalize hm1 : Nat.log 2 p1 = m at *
    rw [← hm] at ht hu hlo2 hhi2
    have hM : 0 < 2 ^ m := Nat.two_pow_pos m
    generalize 2 ^ m = M at *
    have ht1 := lt_add_of_div_eq hM ht
    have ht2 := lt_add_of_div_eq hM ht.symm
    have hu1 := lt_add_of_div_eq hM hu
    have hu2 := lt_add_of_div_eq hM hu.symm
    -- the two `3p`-windows around `i` overlap in at least `p1 + p2` positions
    have hov := run_eq_of_overlap S hR1 hR2
      (c := max (min i (r1.2 + 1 - 3 * p1)) (min i (r2.2 + 1 - 3 * p2)))
      (d := min (min i (r1.2 + 1 - 3 * p1) + 3 * p1 - 1) (min i (r2.2 + 1 - 3 * p2) + 3 * p2 - 1))
      (by omega) (by omega) (by omega) (by omega) (by omega)
    exact Prod.ext hov.1 hov.2

end Lemma85

end DynLZ77.Main.Aux
namespace DynLZ77.Main.Aux

theorem natLog_le_L (n : ℕ) : ((Nat.log 2 n + 1 : ℕ) : ℝ) ≤ 1 + Real.logb 2 (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [h, Nat.log_zero_right, Nat.cast_zero, Real.logb_zero]
    norm_num
  · have hpow : ((2 : ℝ) ^ ((Nat.log 2 n : ℕ) : ℝ)) ≤ (n : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast Nat.pow_log_le_self 2 h.ne'
    have hle : ((Nat.log 2 n : ℕ) : ℝ) ≤ Real.logb 2 (n : ℝ) :=
      (Real.le_logb_iff_rpow_le one_lt_two (by exact_mod_cast h)).2 hpow
    push_cast
    linarith

end DynLZ77.Main.Aux

open DynLZ77.Main

open Classical in
/-- **Lemma 8.5** ([BGS24, Lemma 8]) with `C = 48`: a highly periodic run `S[a..b]` with period
`p` containing `i` is determined by `⌊log₂ p⌋`, the quarter of `[2^m, 2^{m+1})` containing `p`
and the half-`2^m` block of a `3p`-window around `i`, since two such runs share at least
`p + p′` positions and coincide by the Fine–Wilf periodicity lemma and maximality. -/
theorem solution : ∃ C : ℝ, ∀ {α : Type} [DecidableEq α] (S : List α) (i : ℕ),
    (((Finset.Icc 1 S.length ×ˢ Finset.Icc 1 S.length).filter (fun r : ℕ × ℕ =>
        IsRun S r.1 r.2 (per (sub S r.1 r.2)) ∧ HighlyPeriodic (sub S r.1 r.2) ∧
          r.1 ≤ i ∧ i ≤ r.2)).card : ℝ) ≤
      C * (1 + Real.logb 2 (S.length : ℝ)) := by
  refine ⟨48, fun {α} _ S i => ?_⟩
  have h := DynLZ77.Main.Aux.card_hpRuns_le S i
  have hL := DynLZ77.Main.Aux.natLog_le_L S.length
  have h' : (((Finset.Icc 1 S.length ×ˢ Finset.Icc 1 S.length).filter (fun r : ℕ × ℕ =>
        IsRun S r.1 r.2 (per (sub S r.1 r.2)) ∧ HighlyPeriodic (sub S r.1 r.2) ∧
          r.1 ≤ i ∧ i ≤ r.2)).card : ℝ) ≤ 48 * ((Nat.log 2 S.length + 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  linarith
