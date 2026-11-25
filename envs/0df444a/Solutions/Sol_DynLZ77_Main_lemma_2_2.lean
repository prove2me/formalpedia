-- Prove2me | solution 1 for DynLZ77.Main.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @shaygo
-- created : 2026-11-25T12:45:16.177737+00:00
-- url     : https://prove2.me/submissions/1eae832b-58c0-4b67-90b4-ccee0f6c0310

import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_DynLZ77_Main_ExtensionPoints
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


/-!
# Lemma 2.2 ([BGK25, Lemma 17]): heavy paths on strings
-/

namespace DynLZ77.Main.Aux

section HeavyPaths

variable {α : Type} [DecidableEq α]

/-! ### Longest common prefixes -/

theorem lcp_comm : ∀ (u v : List α), lcp u v = lcp v u
  | [], v => by rw [lcp_nil_left, lcp_nil_right]
  | a :: u, [] => by rw [lcp_nil_left, lcp_nil_right]
  | a :: u, b :: v => by
      rw [lcp_cons_cons, lcp_cons_cons, lcp_comm u v]
      by_cases h : a = b
      · subst h
        rfl
      · rw [if_neg h, if_neg (Ne.symm h)]

theorem lcp_le_length_right' (u v : List α) : lcp u v ≤ v.length := by
  rw [lcp_comm]
  exact lcp_le_length_left v u

theorem take_eq_of_lcp (u v : List α) : u.take (lcp u v) = v.take (lcp u v) :=
  ((le_lcp_iff _ u v).1 le_rfl).2.2

/-- Two lists agreeing on their first `m` letters and on the letter at position `m` have a longest
common prefix longer than `m`. -/
theorem lt_lcp_of (u v : List α) {m : ℕ} (htake : u.take m = v.take m) (hu : m < u.length)
    (hv : m < v.length) (hm : u[m]? = v[m]?) : m < lcp u v := by
  have h : m + 1 ≤ lcp u v :=
    (le_lcp_iff (m + 1) u v).2 ⟨hu, hv, by rw [List.take_add_one, List.take_add_one, htake, hm]⟩
  omega

/-! ### Subtree sizes and a heavy-child choice -/

/-- The size of the trie node `w` over the strings `x k`, `k ∈ I`: how many of them start
with `w`. -/
def tsize (x : ℕ → List α) (I : Finset ℕ) (w : List α) : ℕ := (I.filter (fun k => w <+: x k)).card

/-- `hv` chooses, at every node `w` with a child, a child letter of maximal subtree size. -/
def IsHeavyChoice (x : ℕ → List α) (I : Finset ℕ) (hv : List α → Option α) : Prop :=
  ∀ w, (∀ k ∈ I, ∀ c, ¬ (w ++ [c] <+: x k)) ∨
    ∃ h, hv w = some h ∧ ∀ c, tsize x I (w ++ [c]) ≤ tsize x I (w ++ [h])

omit [DecidableEq α] in
theorem getElem?_of_prefix {w : List α} {c : α} {l : List α} (h : w ++ [c] <+: l) :
    l[w.length]? = some c := by
  obtain ⟨t, rfl⟩ := h
  simp

theorem exists_heavyChoice (x : ℕ → List α) (I : Finset ℕ) : ∃ hv, IsHeavyChoice x I hv := by
  have hex : ∀ w : List α, ∃ o : Option α, (∀ k ∈ I, ∀ c, ¬ (w ++ [c] <+: x k)) ∨
      ∃ h, o = some h ∧ ∀ c, tsize x I (w ++ [c]) ≤ tsize x I (w ++ [h]) := by
    intro w
    by_cases hch : ∃ k ∈ I, ∃ c, w ++ [c] <+: x k
    · obtain ⟨k0, hk0, c0, hc0⟩ := hch
      have hmem : some c0 ∈ (((I.filter (fun k => w <+: x k)).image
          (fun k => (x k)[w.length]?)).filter (fun o => o.isSome)) := by
        rw [Finset.mem_filter, Finset.mem_image]
        refine ⟨⟨k0, Finset.mem_filter.2 ⟨hk0, (List.prefix_append w [c0]).trans hc0⟩,
          getElem?_of_prefix hc0⟩, rfl⟩
      obtain ⟨o, ho, hmax⟩ := Finset.exists_max_image
        (((I.filter (fun k => w <+: x k)).image (fun k => (x k)[w.length]?)).filter
          (fun o => o.isSome)) (fun o => tsize x I (w ++ o.toList)) ⟨_, hmem⟩
      rw [Finset.mem_filter] at ho
      obtain ⟨h, rfl⟩ := Option.isSome_iff_exists.1 ho.2
      refine ⟨some h, Or.inr ⟨h, rfl, fun c => ?_⟩⟩
      by_cases hc : ∃ k ∈ I, w ++ [c] <+: x k
      · obtain ⟨k, hk, hck⟩ := hc
        have hcm : some c ∈ (((I.filter (fun k => w <+: x k)).image
            (fun k => (x k)[w.length]?)).filter (fun o => o.isSome)) := by
          rw [Finset.mem_filter, Finset.mem_image]
          exact ⟨⟨k, Finset.mem_filter.2 ⟨hk, (List.prefix_append w [c]).trans hck⟩,
            getElem?_of_prefix hck⟩, rfl⟩
        exact hmax _ hcm
      · have h0 : tsize x I (w ++ [c]) = 0 := by
          unfold tsize
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          exact fun k hk hp => hc ⟨k, hk, hp⟩
        omega
    · refine ⟨none, Or.inl fun k hk c hp => hch ⟨k, hk, c, hp⟩⟩
  choose hv hhv using hex
  exact ⟨hv, hhv⟩

/-- A light edge `w → w ++ [c]` at most halves the subtree size. -/
theorem two_mul_tsize_le (x : ℕ → List α) (I : Finset ℕ) {hv : List α → Option α}
    (hH : IsHeavyChoice x I hv) (w : List α) (c : α) (hc : ∃ k ∈ I, w ++ [c] <+: x k)
    (hl : hv w ≠ some c) : 2 * tsize x I (w ++ [c]) ≤ tsize x I w := by
  rcases hH w with hno | ⟨h, hhv, hmax⟩
  · obtain ⟨k, hk, hck⟩ := hc
    exact absurd hck (hno k hk c)
  · have hne : h ≠ c := fun e => hl (by rw [hhv, e])
    have hdisj : Disjoint (I.filter (fun k => w ++ [c] <+: x k))
        (I.filter (fun k => w ++ [h] <+: x k)) := by
      rw [Finset.disjoint_filter]
      intro k _ h1 h2
      have e := (getElem?_of_prefix h1).symm.trans (getElem?_of_prefix h2)
      exact hne (Option.some_injective _ e).symm
    have hsub : (I.filter (fun k => w ++ [c] <+: x k)) ∪ (I.filter (fun k => w ++ [h] <+: x k)) ⊆
        I.filter (fun k => w <+: x k) := by
      intro k hk
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hk
      rw [Finset.mem_filter]
      rcases hk with ⟨hk, hp⟩ | ⟨hk, hp⟩
      · exact ⟨hk, (List.prefix_append w [c]).trans hp⟩
      · exact ⟨hk, (List.prefix_append w [h]).trans hp⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at h1
    have h2 := hmax c
    unfold tsize at h2 ⊢
    omega

/-! ### Heads of heavy paths along one string -/

/-- `hl hv x m`: the depth of the head of the heavy path through the node `x.take m`, i.e. the
last position `k ≤ m` whose incoming edge is light (`0` for the root). -/
def hl (hv : List α → Option α) (x : List α) (m : ℕ) : ℕ :=
  Nat.findGreatest (fun k => k = 0 ∨ hv (x.take (k - 1)) ≠ x[k - 1]?) m

theorem hl_le (hv : List α → Option α) (x : List α) (m : ℕ) : hl hv x m ≤ m :=
  Nat.findGreatest_le m

theorem hl_spec (hv : List α → Option α) (x : List α) (m : ℕ) :
    hl hv x m = 0 ∨ hv (x.take (hl hv x m - 1)) ≠ x[hl hv x m - 1]? :=
  Nat.findGreatest_spec (P := fun k => k = 0 ∨ hv (x.take (k - 1)) ≠ x[k - 1]?)
    (Nat.zero_le m) (Or.inl rfl)

/-- Two nodes `x.take m`, `x.take m′` (`m < m′`) on the same heavy path: the edge leaving
`x.take m` towards `x` is heavy. -/
theorem heavy_of_hl_eq (hv : List α → Option α) (x : List α) {m m' : ℕ} (hmm' : m < m')
    (heq : hl hv x m = hl hv x m') : hv (x.take m) = x[m]? := by
  have hle := hl_le hv x m
  have h := Nat.findGreatest_is_greatest
    (P := fun k => k = 0 ∨ hv (x.take (k - 1)) ≠ x[k - 1]?) (k := m + 1) (n := m')
    (by unfold hl at heq hle; omega) (by omega)
  simp only [not_or, ne_eq, not_not] at h
  simpa using h.2

/-- The heads met by the root path of `x`. -/
def heads (hv : List α → Option α) (x : List α) : Finset ℕ :=
  (Finset.range (x.length + 1)).image (hl hv x)

/-- The light edges on the root path of `x` (by the depth of their lower end). -/
def lights (hv : List α → Option α) (x : List α) : Finset ℕ :=
  (Finset.Icc 1 x.length).filter (fun k => hv (x.take (k - 1)) ≠ x[k - 1]?)

theorem card_heads_le (hv : List α → Option α) (x : List α) :
    (heads hv x).card ≤ (lights hv x).card + 1 := by
  have hsub : heads hv x ⊆ insert 0 (lights hv x) := by
    intro k hk
    rw [heads, Finset.mem_image] at hk
    obtain ⟨m, hm, rfl⟩ := hk
    rw [Finset.mem_range] at hm
    by_cases hz : hl hv x m = 0
    · rw [hz]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [lights, Finset.mem_filter, Finset.mem_Icc]
      have := hl_le hv x m
      exact ⟨⟨by omega, by omega⟩, (hl_spec hv x m).resolve_left hz⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- The root path of `x i`, `i ∈ I`, has at most `log₂ |I|` light edges. -/
theorem card_lights_le (x : ℕ → List α) (I : Finset ℕ) {hv : List α → Option α}
    (hH : IsHeavyChoice x I hv) {i : ℕ} (hi : i ∈ I) :
    (lights hv (x i)).card ≤ Nat.log 2 I.card := by
  have key : ∀ k, k ≤ (x i).length →
      2 ^ ((lights hv (x i)).filter (· ≤ k)).card * tsize x I ((x i).take k) ≤ I.card := by
    intro k
    induction k with
    | zero =>
      intro _
      have h0 : (lights hv (x i)).filter (· ≤ 0) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro a ha
        rw [lights, Finset.mem_filter, Finset.mem_Icc] at ha
        omega
      rw [h0, Finset.card_empty, pow_zero, one_mul]
      exact Finset.card_filter_le _ _
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      obtain ⟨c, hc⟩ : ∃ c, (x i)[k]? = some c :=
        ⟨(x i)[k], List.getElem?_eq_getElem (by omega)⟩
      have htake : (x i).take (k + 1) = (x i).take k ++ [c] := by
        rw [List.take_add_one, hc]
        rfl
      have hpre : (x i).take k ++ [c] <+: x i := by
        rw [← htake]
        exact List.take_prefix _ _
      have hmono : tsize x I ((x i).take (k + 1)) ≤ tsize x I ((x i).take k) := by
        apply Finset.card_le_card
        intro a ha
        rw [Finset.mem_filter] at ha ⊢
        refine ⟨ha.1, (List.prefix_iff_eq_take.2 ?_).trans ha.2⟩
        rw [htake, List.take_append_of_le_length (by simp)]
        simp
      by_cases hlt : hv ((x i).take k) ≠ some c
      · have hmem : k + 1 ∈ lights hv (x i) := by
          rw [lights, Finset.mem_filter, Finset.mem_Icc, Nat.add_sub_cancel, hc]
          exact ⟨⟨by omega, hk⟩, hlt⟩
        have hfilt : (lights hv (x i)).filter (· ≤ k + 1) =
            insert (k + 1) ((lights hv (x i)).filter (· ≤ k)) := by
          ext a
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨ha, ha'⟩
            by_cases hak : a = k + 1
            · exact Or.inl hak
            · exact Or.inr ⟨ha, by omega⟩
          · rintro (rfl | ⟨ha, ha'⟩)
            · exact ⟨hmem, le_rfl⟩
            · exact ⟨ha, by omega⟩
        rw [hfilt, Finset.card_insert_of_notMem (by simp), pow_succ]
        have h2 := two_mul_tsize_le x I hH ((x i).take k) c ⟨i, hi, hpre⟩ hlt
        rw [← htake] at h2
        calc 2 ^ ((lights hv (x i)).filter (· ≤ k)).card * 2 * tsize x I ((x i).take (k + 1))
            = 2 ^ ((lights hv (x i)).filter (· ≤ k)).card * (2 * tsize x I ((x i).take (k + 1))) :=
              Nat.mul_assoc _ _ _
          _ ≤ 2 ^ ((lights hv (x i)).filter (· ≤ k)).card * tsize x I ((x i).take k) :=
              Nat.mul_le_mul_left _ h2
          _ ≤ I.card := ih'
      · push Not at hlt
        have hfilt : (lights hv (x i)).filter (· ≤ k + 1) = (lights hv (x i)).filter (· ≤ k) := by
          ext a
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨ha, ha'⟩
            refine ⟨ha, ?_⟩
            by_contra hak
            have hak' : a = k + 1 := by omega
            rw [hak', lights, Finset.mem_filter, Nat.add_sub_cancel, hc] at ha
            exact ha.2 hlt
          · rintro ⟨ha, ha'⟩
            exact ⟨ha, by omega⟩
        rw [hfilt]
        exact (Nat.mul_le_mul_left _ hmono).trans ih'
  have h := key (x i).length le_rfl
  have hall : (lights hv (x i)).filter (· ≤ (x i).length) = lights hv (x i) := by
    rw [Finset.filter_eq_self]
    intro a ha
    rw [lights, Finset.mem_filter, Finset.mem_Icc] at ha
    exact ha.1.2
  have hpos : 1 ≤ tsize x I ((x i).take (x i).length) := by
    rw [List.take_length]
    exact Finset.card_pos.2 ⟨i, Finset.mem_filter.2 ⟨hi, List.prefix_refl _⟩⟩
  rw [hall] at h
  exact Nat.le_log_of_pow_le Nat.one_lt_two (le_trans (Nat.le_mul_of_pos_right _ hpos) h)

theorem card_heads_le_log (x : ℕ → List α) (I : Finset ℕ) {hv : List α → Option α}
    (hH : IsHeavyChoice x I hv) {i : ℕ} (hi : i ∈ I) :
    (heads hv (x i)).card ≤ Nat.log 2 I.card + 1 :=
  (card_heads_le hv (x i)).trans (Nat.add_le_add_right (card_lights_le x I hH hi) 1)

/-- **The heavy-path step.** If `a` and `b` both leave their branch point with `c` along the
heavy edge, and both branch points lie on the same heavy path of `c`, then `b` shares a longer
prefix with `a` than with `c`. -/
theorem lcp_lt_of_heavy (hv : List α → Option α) (a b c : List α)
    (ha : hv (a.take (lcp a c)) = a[lcp a c]? ∧ lcp a c < a.length)
    (hb : hv (b.take (lcp b c)) = b[lcp b c]? ∧ lcp b c < b.length)
    (hhead : hl hv c (lcp a c) = hl hv c (lcp b c)) : lcp b c < lcp b a := by
  have hac := take_eq_of_lcp a c
  have hbc := take_eq_of_lcp b c
  have hca := lcp_le_length_right' a c
  have hcb := lcp_le_length_right' b c
  have hmm : lcp a c = lcp b c := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hc := heavy_of_hl_eq hv c h hhead
      have : lcp a c < lcp a c :=
        lt_lcp_of a c hac ha.2 (by omega) (by rw [← ha.1, hac, hc])
      omega
    · have hc := heavy_of_hl_eq hv c h hhead.symm
      have : lcp b c < lcp b c :=
        lt_lcp_of b c hbc hb.2 (by omega) (by rw [← hb.1, hbc, hc])
      omega
  rw [hmm] at ha hac
  exact lt_lcp_of b a (hbc.trans hac.symm) hb.2 ha.2 (by rw [← hb.1, ← ha.1, hbc, hac])

end HeavyPaths

/-! ### Charging the non-dominated extension points -/

section Charging

variable {α : Type} [DecidableEq α]

theorem mem_dext {S : List α} {I : Finset ℕ} {i : ℕ} {q : ℕ × ℕ} (hq : q ∈ dext S I i) :
    q ∈ ext S I i ∧ (∃ j ∈ I, j < i ∧ extPoint S i j = q) ∧
      ∀ q' ∈ ext S I i, q' ≠ q → ¬ (q.1 ≤ q'.1 ∧ q.2 ≤ q'.2) := by
  unfold dext nonDominated at hq
  rw [Finset.mem_filter] at hq
  refine ⟨hq.1, ?_, hq.2⟩
  have h := hq.1
  unfold ext at h
  rw [Finset.mem_image] at h
  obtain ⟨j, hj, hjq⟩ := h
  rw [Finset.mem_filter] at hj
  exact ⟨j, hj.1, hj.2, hjq⟩

/-- Non-dominated points have pairwise distinct second coordinates. -/
theorem dext_eq_of_snd {S : List α} {I : Finset ℕ} {i : ℕ} {q q' : ℕ × ℕ}
    (hq : q ∈ dext S I i) (hq' : q' ∈ dext S I i) (h : q.2 = q'.2) : q = q' := by
  by_contra hne
  have h1 := (mem_dext hq).2.2 q' (mem_dext hq').1 (Ne.symm hne)
  have h2 := (mem_dext hq').2.2 q (mem_dext hq).1 hne
  omega

/-- Non-dominated points have pairwise distinct first coordinates. -/
theorem dext_eq_of_fst {S : List α} {I : Finset ℕ} {i : ℕ} {q q' : ℕ × ℕ}
    (hq : q ∈ dext S I i) (hq' : q' ∈ dext S I i) (h : q.1 = q'.1) : q = q' := by
  by_contra hne
  have h1 := (mem_dext hq).2.2 q' (mem_dext hq').1 (Ne.symm hne)
  have h2 := (mem_dext hq').2.2 q (mem_dext hq).1 hne
  omega

theorem snd_le_of_mem_dext {S : List α} {I : Finset ℕ} {i : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ dext S I i) : q.2 ≤ (S.drop (i - 1)).length := by
  obtain ⟨j, -, -, rfl⟩ := (mem_dext hq).2.1
  exact lcp_le_length_left _ _

theorem fst_le_of_mem_dext {S : List α} {I : Finset ℕ} {i : ℕ} {q : ℕ × ℕ}
    (hq : q ∈ dext S I i) : q.1 ≤ (S.take i).reverse.length := by
  obtain ⟨j, -, -, rfl⟩ := (mem_dext hq).2.1
  exact lcp_le_length_left _ _

/-- Type 1 through the suffix trie: the branch point of `q` is the deepest one of `DExt(i)` on its
heavy path. -/
def type1R (S : List α) (I : Finset ℕ) (hvR : List α → Option α) (i : ℕ) (q : ℕ × ℕ) : Prop :=
  ∀ q'' ∈ dext S I i, q.2 < q''.2 → hl hvR (S.drop (i - 1)) q''.2 ≠ hl hvR (S.drop (i - 1)) q.2

/-- Type 1 through the reversed-prefix trie. -/
def type1L (S : List α) (I : Finset ℕ) (hvL : List α → Option α) (i : ℕ) (q : ℕ × ℕ) : Prop :=
  ∀ q'' ∈ dext S I i, q.1 < q''.1 →
    hl hvL (S.take i).reverse q''.1 ≠ hl hvL (S.take i).reverse q.1

open Classical in
theorem card_type1R_le (S : List α) (I : Finset ℕ) (hvR : List α → Option α) (i : ℕ) :
    ((dext S I i).filter (type1R S I hvR i)).card ≤ (heads hvR (S.drop (i - 1))).card := by
  apply Finset.card_le_card_of_injOn (fun q => hl hvR (S.drop (i - 1)) q.2)
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    rw [Finset.mem_coe, heads, Finset.mem_image]
    exact ⟨q.2, Finset.mem_range.2 (Nat.lt_succ_of_le (snd_le_of_mem_dext hq.1)), rfl⟩
  · intro q hq q' hq' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hq hq'
    by_contra hne
    have h2 : q.2 ≠ q'.2 := fun e => hne (dext_eq_of_snd hq.1 hq'.1 e)
    rcases lt_or_gt_of_ne h2 with h | h
    · exact hq.2 q' hq'.1 h heq.symm
    · exact hq'.2 q hq.1 h heq

open Classical in
theorem card_type1L_le (S : List α) (I : Finset ℕ) (hvL : List α → Option α) (i : ℕ) :
    ((dext S I i).filter (type1L S I hvL i)).card ≤ (heads hvL (S.take i).reverse).card := by
  apply Finset.card_le_card_of_injOn (fun q => hl hvL (S.take i).reverse q.1)
  · intro q hq
    rw [Finset.mem_coe, Finset.mem_filter] at hq
    rw [Finset.mem_coe, heads, Finset.mem_image]
    exact ⟨q.1, Finset.mem_range.2 (Nat.lt_succ_of_le (fst_le_of_mem_dext hq.1)), rfl⟩
  · intro q hq q' hq' heq
    rw [Finset.mem_coe, Finset.mem_filter] at hq hq'
    by_contra hne
    have h1 : q.1 ≠ q'.1 := fun e => hne (dext_eq_of_fst hq.1 hq'.1 e)
    rcases lt_or_gt_of_ne h1 with h | h
    · exact hq.2 q' hq'.1 h heq.symm
    · exact hq'.2 q hq.1 h heq

/-- A type-2 point leaves its branch point along the heavy edge (suffix trie). -/
theorem heavy_of_not_type1R {S : List α} {I : Finset ℕ} {hvR : List α → Option α} {i j : ℕ}
    (h : ¬ type1R S I hvR i (extPoint S i j)) :
    hvR ((S.drop (i - 1)).take (lcp (S.drop (i - 1)) (S.drop (j - 1)))) =
        (S.drop (i - 1))[lcp (S.drop (i - 1)) (S.drop (j - 1))]? ∧
      lcp (S.drop (i - 1)) (S.drop (j - 1)) < (S.drop (i - 1)).length := by
  unfold type1R at h
  push Not at h
  obtain ⟨q'', hq'', hlt, heq⟩ := h
  have hle := snd_le_of_mem_dext hq''
  exact ⟨heavy_of_hl_eq hvR (S.drop (i - 1)) hlt heq.symm, lt_of_lt_of_le hlt hle⟩

/-- A type-2 point leaves its branch point along the heavy edge (reversed-prefix trie). -/
theorem heavy_of_not_type1L {S : List α} {I : Finset ℕ} {hvL : List α → Option α} {i j : ℕ}
    (h : ¬ type1L S I hvL i (extPoint S i j)) :
    hvL ((S.take i).reverse.take (lcp (S.take i).reverse (S.take j).reverse)) =
        (S.take i).reverse[lcp (S.take i).reverse (S.take j).reverse]? ∧
      lcp (S.take i).reverse (S.take j).reverse < (S.take i).reverse.length := by
  unfold type1L at h
  push Not at h
  obtain ⟨q'', hq'', hlt, heq⟩ := h
  have hle := fst_le_of_mem_dext hq''
  exact ⟨heavy_of_hl_eq hvL (S.take i).reverse hlt heq.symm, lt_of_lt_of_le hlt hle⟩

/-- **The charging claim** (proof of [BGK25, Lemma 17]): two type-2 points `p_{i,j}`, `p_{i′,j}`
(`i < i′`) charged to the same `j` cannot sit on the same pair of heavy paths, since otherwise
`p_{i′,i}` would strictly dominate `p_{i′,j}`. -/
theorem type2_claim (S : List α) (I : Finset ℕ) (hvR hvL : List α → Option α) {i i' j : ℕ}
    (hii' : i < i') (hiI : i ∈ I)
    (h2R : ¬ type1R S I hvR i (extPoint S i j)) (h2L : ¬ type1L S I hvL i (extPoint S i j))
    (hq' : extPoint S i' j ∈ dext S I i')
    (h2R' : ¬ type1R S I hvR i' (extPoint S i' j)) (h2L' : ¬ type1L S I hvL i' (extPoint S i' j))
    (hR : hl hvR (S.drop (j - 1)) (lcp (S.drop (i - 1)) (S.drop (j - 1))) =
      hl hvR (S.drop (j - 1)) (lcp (S.drop (i' - 1)) (S.drop (j - 1))))
    (hL : hl hvL (S.take j).reverse (lcp (S.take i).reverse (S.take j).reverse) =
      hl hvL (S.take j).reverse (lcp (S.take i').reverse (S.take j).reverse)) : False := by
  have hRlt := lcp_lt_of_heavy hvR (S.drop (i - 1)) (S.drop (i' - 1)) (S.drop (j - 1))
    (heavy_of_not_type1R h2R) (heavy_of_not_type1R h2R') hR
  have hLlt := lcp_lt_of_heavy hvL (S.take i).reverse (S.take i').reverse (S.take j).reverse
    (heavy_of_not_type1L h2L) (heavy_of_not_type1L h2L') hL
  have hmem : extPoint S i' i ∈ ext S I i' := by
    unfold ext
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨hiI, hii'⟩)
  have hne : extPoint S i' i ≠ extPoint S i' j := by
    intro e
    have := congrArg Prod.snd e
    unfold extPoint lcpAt at this
    simp only at this
    omega
  apply (mem_dext hq').2.2 _ hmem hne
  unfold extPoint lcpAt lcsAt
  exact ⟨le_of_lt hLlt, le_of_lt hRlt⟩

end Charging

/-! ### Counting -/

section Counting

variable {α : Type} [DecidableEq α]

open Classical in
/-- A witness `j ∈ I`, `j < i`, of a point of `Ext_I(i)`. -/
noncomputable def wit (S : List α) (I : Finset ℕ) (i : ℕ) (q : ℕ × ℕ) : ℕ :=
  if h : ∃ j ∈ I, j < i ∧ extPoint S i j = q then Classical.choose h else 0

theorem wit_spec {S : List α} {I : Finset ℕ} {i : ℕ} {q : ℕ × ℕ} (hq : q ∈ dext S I i) :
    wit S I i q ∈ I ∧ wit S I i q < i ∧ extPoint S i (wit S I i q) = q := by
  have h := (mem_dext hq).2.1
  unfold wit
  rw [dif_pos h]
  exact Classical.choose_spec h

open Classical in
/-- The type-2 points of `DExt_I(i)`. -/
noncomputable def T2 (S : List α) (I : Finset ℕ) (hvR hvL : List α → Option α) (i : ℕ) :
    Finset (ℕ × ℕ) :=
  (dext S I i).filter (fun q => ¬ type1R S I hvR i q ∧ ¬ type1L S I hvL i q)

open Classical in
theorem mem_T2 {S : List α} {I : Finset ℕ} {hvR hvL : List α → Option α} {i : ℕ} {q : ℕ × ℕ}
    (h : q ∈ T2 S I hvR hvL i) :
    q ∈ dext S I i ∧ ¬ type1R S I hvR i q ∧ ¬ type1L S I hvL i q := by
  unfold T2 at h
  exact Finset.mem_filter.1 h

open Classical in
theorem card_dext_le (S : List α) (I : Finset ℕ) (hvR hvL : List α → Option α) (i : ℕ) :
    (dext S I i).card ≤ (heads hvR (S.drop (i - 1))).card + (heads hvL (S.take i).reverse).card
      + (T2 S I hvR hvL i).card := by
  have hsub : dext S I i ⊆ ((dext S I i).filter (type1R S I hvR i) ∪
      (dext S I i).filter (type1L S I hvL i)) ∪ T2 S I hvR hvL i := by
    intro q hq
    by_cases hR : type1R S I hvR i q
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hq, hR⟩))
    · by_cases hL : type1L S I hvL i q
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hq, hL⟩))
      · refine Finset.mem_union_right _ ?_
        unfold T2
        exact Finset.mem_filter.2 ⟨hq, hR, hL⟩
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le ((dext S I i).filter (type1R S I hvR i) ∪
      (dext S I i).filter (type1L S I hvL i)) (T2 S I hvR hvL i)
  have h3 := Finset.card_union_le ((dext S I i).filter (type1R S I hvR i))
      ((dext S I i).filter (type1L S I hvL i))
  have h4 := card_type1R_le S I hvR i
  have h5 := card_type1L_le S I hvL i
  omega

/-- **Charging type-2 points** to (witness, head on the reversed-prefix trie, head on the suffix
trie): injective by `type2_claim`. -/
theorem card_T2_le (S : List α) (I : Finset ℕ) (hvR hvL : List α → Option α) :
    ∑ i ∈ I, (T2 S I hvR hvL i).card ≤
      ∑ j ∈ I, (heads hvL (S.take j).reverse).card * (heads hvR (S.drop (j - 1))).card := by
  have hcod : ∑ j ∈ I, (heads hvL (S.take j).reverse).card * (heads hvR (S.drop (j - 1))).card
      = (I.sigma (fun j => heads hvL (S.take j).reverse ×ˢ heads hvR (S.drop (j - 1)))).card := by
    rw [Finset.card_sigma]
    simp only [Finset.card_product]
  rw [hcod, ← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun p => (⟨wit S I p.1 p.2,
      (hl hvL (S.take (wit S I p.1 p.2)).reverse p.2.1,
        hl hvR (S.drop (wit S I p.1 p.2 - 1)) p.2.2)⟩ : Σ _ : ℕ, ℕ × ℕ))
  · rintro ⟨i, q⟩ hp
    simp only [Finset.mem_coe, Finset.mem_sigma] at hp
    simp only [Finset.mem_coe, Finset.mem_sigma]
    obtain ⟨-, hq⟩ := hp
    obtain ⟨hw, -, hwq⟩ := wit_spec (mem_T2 hq).1
    generalize wit S I i q = j at hw hwq ⊢
    subst hwq
    refine ⟨hw, Finset.mem_product.2 ⟨?_, ?_⟩⟩
    · rw [heads, Finset.mem_image]
      exact ⟨lcp (S.take i).reverse (S.take j).reverse,
        Finset.mem_range.2 (Nat.lt_succ_of_le (lcp_le_length_right' _ _)), rfl⟩
    · rw [heads, Finset.mem_image]
      exact ⟨lcp (S.drop (i - 1)) (S.drop (j - 1)),
        Finset.mem_range.2 (Nat.lt_succ_of_le (lcp_le_length_right' _ _)), rfl⟩
  · rintro ⟨i, q⟩ hp ⟨i', q'⟩ hp' heq
    simp only [Finset.mem_coe, Finset.mem_sigma] at hp hp'
    obtain ⟨hi, hq⟩ := hp
    obtain ⟨hi', hq'⟩ := hp'
    obtain ⟨hqD, hqR, hqL⟩ := mem_T2 hq
    obtain ⟨hqD', hqR', hqL'⟩ := mem_T2 hq'
    obtain ⟨-, -, hjq⟩ := wit_spec hqD
    obtain ⟨-, -, hjq'⟩ := wit_spec hqD'
    simp only [Sigma.mk.inj_iff, heq_iff_eq, Prod.mk.injEq] at heq
    obtain ⟨hw, hL, hR⟩ := heq
    rw [← hw] at hjq' hL hR
    generalize wit S I i q = j at hjq hjq' hL hR
    subst hjq hjq'
    rcases lt_trichotomy i i' with h | h | h
    · exact (type2_claim S I hvR hvL h hi hqR hqL hqD' hqR' hqL' hR hL).elim
    · subst h
      rfl
    · exact (type2_claim S I hvR hvL h hi' hqR' hqL' hqD hqR hqL hR.symm hL.symm).elim

/-- **[BGK25, Lemma 17], counting form**: `∑ |DExt_I(i)| ≤ |I|·2(L+1) + |I|·(L+1)²`,
`L = ⌊log₂ |I|⌋`. -/
theorem sum_dext_le (S : List α) (I : Finset ℕ) :
    ∑ i ∈ I, (dext S I i).card ≤ I.card * (2 * (Nat.log 2 I.card + 1)) +
      I.card * (Nat.log 2 I.card + 1) ^ 2 := by
  obtain ⟨hvR, hR⟩ := exists_heavyChoice (fun k => S.drop (k - 1)) I
  obtain ⟨hvL, hL⟩ := exists_heavyChoice (fun k => (S.take k).reverse) I
  have hRi : ∀ i ∈ I, (heads hvR (S.drop (i - 1))).card ≤ Nat.log 2 I.card + 1 :=
    fun i hi => card_heads_le_log (fun k => S.drop (k - 1)) I hR hi
  have hLi : ∀ i ∈ I, (heads hvL (S.take i).reverse).card ≤ Nat.log 2 I.card + 1 :=
    fun i hi => card_heads_le_log (fun k => (S.take k).reverse) I hL hi
  calc ∑ i ∈ I, (dext S I i).card
      ≤ ∑ i ∈ I, ((heads hvR (S.drop (i - 1))).card + (heads hvL (S.take i).reverse).card
          + (T2 S I hvR hvL i).card) :=
        Finset.sum_le_sum (fun i _ => card_dext_le S I hvR hvL i)
    _ = ∑ i ∈ I, ((heads hvR (S.drop (i - 1))).card + (heads hvL (S.take i).reverse).card)
          + ∑ i ∈ I, (T2 S I hvR hvL i).card := Finset.sum_add_distrib
    _ ≤ ∑ i ∈ I, 2 * (Nat.log 2 I.card + 1) + ∑ j ∈ I, (heads hvL (S.take j).reverse).card *
          (heads hvR (S.drop (j - 1))).card :=
        Nat.add_le_add (Finset.sum_le_sum (fun i hi => by
          have := hRi i hi
          have := hLi i hi
          omega)) (card_T2_le S I hvR hvL)
    _ ≤ ∑ i ∈ I, 2 * (Nat.log 2 I.card + 1) + ∑ j ∈ I, (Nat.log 2 I.card + 1) ^ 2 :=
        Nat.add_le_add_left (Finset.sum_le_sum (fun j hj => by
          rw [pow_two]
          exact Nat.mul_le_mul (hLi j hj) (hRi j hj))) _
    _ = I.card * (2 * (Nat.log 2 I.card + 1)) + I.card * (Nat.log 2 I.card + 1) ^ 2 := by
        rw [Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]

end Counting

end DynLZ77.Main.Aux

/-!
# Lemma 2.2: the real-valued bound
-/

namespace DynLZ77.Main.Aux

section Final

variable {α : Type} [DecidableEq α]

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

/-- **Lemma 2.2** with `C = 3`. -/
theorem lemma_2_2_main : ∃ C : ℝ, ∀ {α : Type} [DecidableEq α] (S : List α) (I : Finset ℕ),
    I ⊆ Finset.Icc 1 S.length →
      ((∑ i ∈ I, (dext S I i).card : ℕ) : ℝ) ≤
        C * (I.card : ℝ) * (1 + Real.logb 2 (S.length : ℝ)) ^ 2 := by
  refine ⟨3, fun {α} _ S I hI => ?_⟩
  have hcard : I.card ≤ S.length := by
    have h := Finset.card_le_card hI
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at h
  have hsum : ((∑ i ∈ I, (dext S I i).card : ℕ) : ℝ) ≤
      (I.card : ℝ) * (2 * ((Nat.log 2 I.card : ℝ) + 1)) +
        (I.card : ℝ) * ((Nat.log 2 I.card : ℝ) + 1) ^ 2 := by
    exact_mod_cast sum_dext_le S I
  have hmono : ((Nat.log 2 I.card : ℕ) : ℝ) ≤ ((Nat.log 2 S.length : ℕ) : ℝ) := by
    exact_mod_cast Nat.log_mono_right hcard
  have hL := natLog_le_L S.length
  push_cast at hL
  have hc : (0 : ℝ) ≤ (I.card : ℝ) := Nat.cast_nonneg _
  have hx0 : (0 : ℝ) ≤ (Nat.log 2 I.card : ℝ) := Nat.cast_nonneg _
  set x : ℝ := (Nat.log 2 I.card : ℝ) + 1 with hx
  set M : ℝ := 1 + Real.logb 2 (S.length : ℝ) with hM
  have hx1 : 1 ≤ x := by linarith
  have hxM : x ≤ M := by linarith
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hxM2 : x ^ 2 ≤ M ^ 2 := by nlinarith
  have ha := mul_le_mul_of_nonneg_left hx2 hc
  have hb := mul_le_mul_of_nonneg_left hxM2 hc
  calc ((∑ i ∈ I, (dext S I i).card : ℕ) : ℝ)
      ≤ (I.card : ℝ) * (2 * x) + (I.card : ℝ) * x ^ 2 := hsum
    _ ≤ 3 * (I.card : ℝ) * M ^ 2 := by nlinarith

end Final

end DynLZ77.Main.Aux

open DynLZ77.Main

/-- **Lemma 2.2** ([BGK25, Lemma 17]): `∑_{i ∈ I} |DExt_I(i,S)| ≤ C·|I|·(1 + log₂|S|)²`, with
`C = 3`, by heavy-path decompositions of the suffix trie and the reversed-prefix trie of `I`. -/
theorem solution : ∃ C : ℝ, ∀ {α : Type} [DecidableEq α] (S : List α) (I : Finset ℕ),
    I ⊆ Finset.Icc 1 S.length →
      ((∑ i ∈ I, (dext S I i).card : ℕ) : ℝ) ≤
        C * (I.card : ℝ) * (1 + Real.logb 2 (S.length : ℝ)) ^ 2 :=
  DynLZ77.Main.Aux.lemma_2_2_main
