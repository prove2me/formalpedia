-- Prove2me | solution 1 for DynLZ77.KK.local_sparse
-- status  : ACCEPTED   (prove)
-- author  : @shaygo
-- created : 2026-11-25T07:30:09.968702+00:00
-- url     : https://prove2.me/submissions/4a9fbf3b-dbb4-4197-b88a-3d4e46704470

import Mathlib.Data.List.PeriodicityLemma
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
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

/-! ## Kempa–Kociumaka, Section 8.2: Facts 8.3 and 8.7, the boundary set, counting -/

namespace DynLZ77.Main.Aux

open DynLZ77.KK

variable {α : Type}

/-- `T[c..d]` is a factor of `T[a..b]` when `a ≤ c` and `d ≤ b`. -/
theorem sub_infix (T : List α) {a b c d : ℕ} (ha : 1 ≤ a) (hac : a ≤ c) (hcd : c ≤ d + 1)
    (hdb : d ≤ b) : sub T c d <:+: sub T a b := by
  have h : sub T c d = ((sub T a b).drop (c - a)).take (d + 1 - c) := by
    unfold sub
    rw [window_window T (by omega), show a - 1 + (c - a) = c - 1 by omega]
  rw [h]
  exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix

/-- A factor has at most the (smallest) period of the string containing it. -/
theorem per_sub_le (T : List α) {a b c d : ℕ} (ha : 1 ≤ a) (hac : a ≤ c) (hcd : c ≤ d + 1)
    (hdb : d ≤ b) : per (sub T c d) ≤ per (sub T a b) := by
  apply per_le_of_isPeriod
  obtain ⟨h1, hP⟩ := (isPeriod_iff_hasPeriod _ _).1 (per_isPeriod (sub T a b))
  exact (isPeriod_iff_hasPeriod _ _).2 ⟨h1, hP.infix (sub_infix T ha hac hcd hdb)⟩

theorem real_le_third_of_le {p τ : ℕ} (h : 3 * p ≤ τ) : (p : ℝ) ≤ (τ : ℝ) / 3 := by
  rw [le_div_iff₀ three_pos]
  exact_mod_cast (by omega : p * 3 ≤ τ)

/-- **Fact 8.3** of [KK19]: two equal length-`τ` fragments at distance at most `τ/3` start in `Q`
(so a class disjoint from `Q` is `τ/3`-sparse). -/
theorem inQ_of_close_repeat (T : List α) {τ j j' : ℕ} (hj : 1 ≤ j) (hjj' : j < j')
    (hd : 3 * (j' - j) ≤ τ) (heq : sub T j (j + τ - 1) = sub T j' (j' + τ - 1)) :
    InQ T τ j := by
  have hτ : 1 ≤ τ := by omega
  have hF : sub T j (j + τ - 1) = (T.drop (j - 1)).take τ := sub_eq_window T hj hτ
  have hF' : sub T j' (j' + τ - 1) = (T.drop (j' - 1)).take τ := sub_eq_window T (by omega) hτ
  have hper : IsPeriod (sub T j (j + τ - 1)) (j' - j) := by
    rw [isPeriod_iff_hasPeriod]
    refine ⟨by omega, ?_⟩
    rw [List.hasPeriod_iff_getElem?]
    intro k hk
    have hlenF : (sub T j (j + τ - 1)).length ≤ τ := by
      rw [hF, List.length_take]
      omega
    have h1 : (sub T j (j + τ - 1))[k]? = T[j' - 1 + k]? := by
      rw [heq, hF', getElem?_window T (by omega)]
    have h2 : (sub T j (j + τ - 1))[k + (j' - j)]? = T[j' - 1 + k]? := by
      rw [hF, getElem?_window T (by omega), show j - 1 + (k + (j' - j)) = j' - 1 + k by omega]
    rw [h1, h2]
  unfold InQ
  exact real_le_third_of_le (by have := per_le_of_isPeriod hper; omega)

/-- The boundary set `B` of [KK19, §8.2.1] (as a predicate on positions): `i ∉ Q`, but one of the
two length-`(τ − 1)` fragments `T[i..i+τ−1)`, `T[i+1..i+τ)` has period at most `τ/3`. -/
def InB (T : List α) (τ i : ℕ) : Prop :=
  ¬ InQ T τ i ∧ (((per (sub T i (i + τ - 2)) : ℝ) ≤ (τ : ℝ) / 3) ∨
    ((per (sub T (i + 1) (i + τ - 1)) : ℝ) ≤ (τ : ℝ) / 3))

/-- A position outside `Q` next to a position in `Q` is in `B`. -/
theorem inB_of_succ (T : List α) {τ i : ℕ} (hτ : 2 ≤ τ) (hi : 1 ≤ i) (hni : ¬ InQ T τ i)
    (hs : InQ T τ (i + 1)) : InB T τ i := by
  refine ⟨hni, Or.inr (le_trans ?_ hs)⟩
  exact_mod_cast per_sub_le T (a := i + 1) (b := i + 1 + τ - 1) (c := i + 1) (d := i + τ - 1)
    (by omega) le_rfl (by omega) (by omega)

theorem inB_of_pred (T : List α) {τ i : ℕ} (hτ : 2 ≤ τ) (hi : 2 ≤ i) (hni : ¬ InQ T τ i)
    (hp : InQ T τ (i - 1)) : InB T τ i := by
  refine ⟨hni, Or.inl (le_trans ?_ hp)⟩
  exact_mod_cast per_sub_le T (a := i - 1) (b := i - 1 + τ - 1) (c := i) (d := i + τ - 2)
    (by omega) (by omega) (by omega) (by omega)

/-- **Fact 8.7** of [KK19]: an interval `[ℓ..r]` that meets `Q` without being contained in it
meets `B`. -/
theorem exists_inB (T : List α) {τ ℓ r : ℕ} (hτ : 2 ≤ τ) (hℓ : 1 ≤ ℓ)
    (hQ : ∃ a, ℓ ≤ a ∧ a ≤ r ∧ InQ T τ a) (hnQ : ∃ b, ℓ ≤ b ∧ b ≤ r ∧ ¬ InQ T τ b) :
    ∃ c, ℓ ≤ c ∧ c ≤ r ∧ InB T τ c := by
  obtain ⟨a, ha1, ha2, haQ⟩ := hQ
  obtain ⟨b, hb1, hb2, hbQ⟩ := hnQ
  -- discrete intermediate value: walking from one end to the other, `Q`-membership flips somewhere
  have flip : ∀ (P : ℕ → Prop) (x t : ℕ), P x → ¬ P (x + t) →
      ∃ s, s < t ∧ P (x + s) ∧ ¬ P (x + s + 1) := by
    intro P x t hx
    induction t with
    | zero => intro h; exact absurd hx h
    | succ t ih =>
      intro h
      by_cases ht : P (x + t)
      · exact ⟨t, by omega, ht, h⟩
      · obtain ⟨s, hs, h1, h2⟩ := ih ht
        exact ⟨s, by omega, h1, h2⟩
  rcases lt_or_gt_of_ne (show a ≠ b by rintro rfl; exact hbQ haQ) with hab | hab
  · obtain ⟨s, hs, h1, h2⟩ := flip (InQ T τ) a (b - a) haQ (by rwa [show a + (b - a) = b by omega])
    exact ⟨a + s + 1, by omega, by omega,
      inB_of_pred T hτ (by omega) h2 (by rwa [show a + s + 1 - 1 = a + s by omega])⟩
  · obtain ⟨s, hs, h1, h2⟩ := flip (fun y => ¬ InQ T τ y) b (a - b) hbQ
      (by simpa [show b + (a - b) = a by omega] using haQ)
    exact ⟨b + s, by omega, by omega,
      inB_of_succ T hτ (by omega) h1 (by simpa using h2)⟩

/-! ### Gluing periodic fragments -/

/-- `hasPeriod_of_windows` with the size condition `p + q ≤ L` on the window length `L` instead of
`3p, 3q ≤ L`: if the first `L` letters of `W` have period `p` and every length-`L` window has a
period `q` with `p + q ≤ L`, then `W` has period `p`. -/
theorem hasPeriod_of_windows' {W : List α} {L p : ℕ} (hL : L ≤ W.length) (hp1 : 1 ≤ p)
    (h0 : (W.take L).HasPeriod p)
    (hwin : ∀ e, e + L ≤ W.length → ∃ q, 1 ≤ q ∧ p + q ≤ L ∧ ((W.drop e).take L).HasPeriod q) :
    W.HasPeriod p := by
  have key : ∀ m, L ≤ m → m ≤ W.length → (W.take m).HasPeriod p := by
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
      · obtain ⟨q, hq1, hpq, hX⟩ := hwin (m + 1 - L) (by omega)
        have hXlen : ((W.drop (m + 1 - L)).take L).length = L := by
          rw [List.length_take, List.length_drop]
          omega
        have hOX : (W.drop (m + 1 - L)).take (L - 1) =
            ((W.drop (m + 1 - L)).take L).take (L - 1) := by
          rw [List.take_take, Nat.min_eq_left (by omega)]
        have hOlen : ((W.drop (m + 1 - L)).take (L - 1)).length = L - 1 := by
          rw [List.length_take, List.length_drop]
          omega
        have hO_q : ((W.drop (m + 1 - L)).take (L - 1)).HasPeriod q := by
          rw [hOX]
          exact hX.infix (List.take_prefix _ _).isInfix
        have hO_p : ((W.drop (m + 1 - L)).take (L - 1)).HasPeriod p := by
          rw [List.hasPeriod_iff_getElem?, hOlen]
          intro k hk
          rw [getElem?_window W (by omega), getElem?_window W (by omega)]
          have h' := ih' (m + 1 - L + k) (by omega)
          rwa [List.getElem?_take, List.getElem?_take, if_pos (by omega), if_pos (by omega),
            show m + 1 - L + k + p = m + 1 - L + (k + p) by omega] at h'
        have hgpos : 1 ≤ Nat.gcd p q := Nat.gcd_pos_of_pos_left q hp1
        have hg := hO_p.gcd hO_q (by rw [hOlen]; omega)
        have hmod : ∀ r, r ≤ L - 1 → Nat.gcd p q ∣ r →
            (L - 1 - r) % Nat.gcd p q = (L - 1) % Nat.gcd p q := by
          intro r hr hgr
          obtain ⟨c, rfl⟩ := hgr
          conv_rhs => rw [show L - 1 = (L - 1 - Nat.gcd p q * c) + Nat.gcd p q * c by omega]
          rw [Nat.add_mul_mod_self_left]
        have hXq := List.hasPeriod_iff_getElem?.1 hX (L - 1 - q) (by rw [hXlen]; omega)
        rw [show L - 1 - q + q = L - 1 by omega] at hXq
        have h1 := hg.getElem?_mod _ (L - 1 - p) _ (by rw [hOlen]; omega)
        have h2 := hg.getElem?_mod _ (L - 1 - q) _ (by rw [hOlen]; omega)
        rw [hmod p (by omega) (Nat.gcd_dvd_left p q)] at h1
        rw [hmod q (by omega) (Nat.gcd_dvd_right p q)] at h2
        have hOpq : ((W.drop (m + 1 - L)).take (L - 1))[L - 1 - p]? =
            ((W.drop (m + 1 - L)).take (L - 1))[L - 1 - q]? := h1.symm.trans h2
        rw [getElem?_window W (by omega), getElem?_window W (by omega)] at hOpq
        rw [getElem?_window W (by omega), getElem?_window W (by omega)] at hXq
        rw [show j + p = m + 1 - L + (L - 1) by omega, show j = m + 1 - L + (L - 1 - p) by omega]
        exact hOpq.trans hXq
  have h := key W.length hL le_rfl
  rwa [List.take_length] at h

theorem window_infix (X : List α) (e L : ℕ) : (X.drop e).take L <:+: X :=
  (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix

/-- Two length-`λ` windows of `T`, starting `d` apart, with periods `p₁` and `p₂`: if their
overlap is long enough (`2p₁ + d ≤ λ` and `p₁ + p₂ + d ≤ λ`), their union has period `p₁`. -/
theorem hasPeriod_glue2 (T : List α) {a d lam p1 p2 : ℕ} (hp1 : 1 ≤ p1) (hp2 : 1 ≤ p2)
    (h11 : 2 * p1 + d ≤ lam) (h12 : p1 + p2 + d ≤ lam) (hfit : a + d + lam ≤ T.length)
    (hF1 : ((T.drop a).take lam).HasPeriod p1)
    (hF2 : ((T.drop (a + d)).take lam).HasPeriod p2) :
    ((T.drop a).take (d + lam)).HasPeriod p1 := by
  have hWlen : ((T.drop a).take (d + lam)).length = d + lam := by
    rw [List.length_take, List.length_drop]
    omega
  apply hasPeriod_of_windows' (L := lam - d) (by rw [hWlen]; omega) hp1
  · have h : ((T.drop a).take (d + lam)).take (lam - d) =
        (((T.drop a).take lam).drop 0).take (lam - d) := by
      rw [List.drop_zero, List.take_take, List.take_take, Nat.min_eq_left (by omega),
        Nat.min_eq_left (by omega)]
    rw [h]
    exact hF1.infix (window_infix _ _ _)
  · intro e he
    rw [hWlen] at he
    rw [window_window T (by omega)]
    by_cases hed : e ≤ d
    · refine ⟨p1, hp1, by omega, ?_⟩
      rw [← window_window T (L := lam) (by omega)]
      exact hF1.infix (window_infix _ _ _)
    · refine ⟨p2, hp2, by omega, ?_⟩
      rw [show a + e = a + d + (e - d) by omega, ← window_window T (L := lam) (by omega)]
      exact hF2.infix (window_infix _ _ _)

/-! ### At most two positions of `B` in a short block (local part of Lemma 8.8 of [KK19]) -/

/-- Two "right-type" boundary candidates `j₁ < j₂` close together force `j₁ ∈ Q`. -/
theorem inQ_of_two_right (T : List α) {τ j1 j2 : ℕ} (hj1 : 1 ≤ j1) (h12 : j1 < j2)
    (hd : 3 * (j2 - j1) + 1 ≤ τ) (hn : j2 + τ - 1 ≤ T.length)
    (h1 : (per (sub T j1 (j1 + τ - 2)) : ℝ) ≤ (τ : ℝ) / 3)
    (h2 : (per (sub T j2 (j2 + τ - 2)) : ℝ) ≤ (τ : ℝ) / 3) : InQ T τ j1 := by
  have hτ : 2 ≤ τ := by omega
  have e1 : sub T j1 (j1 + τ - 2) = (T.drop (j1 - 1)).take (τ - 1) := by
    rw [show j1 + τ - 2 = j1 + (τ - 1) - 1 by omega]
    exact sub_eq_window T hj1 (by omega)
  have e2 : sub T j2 (j2 + τ - 2) = (T.drop (j1 - 1 + (j2 - j1))).take (τ - 1) := by
    rw [show j2 + τ - 2 = j2 + (τ - 1) - 1 by omega, show j1 - 1 + (j2 - j1) = j2 - 1 by omega]
    exact sub_eq_window T (by omega) (by omega)
  obtain ⟨hp1, hP1⟩ := (isPeriod_iff_hasPeriod _ _).1 (per_isPeriod (sub T j1 (j1 + τ - 2)))
  obtain ⟨hp2, hP2⟩ := (isPeriod_iff_hasPeriod _ _).1 (per_isPeriod (sub T j2 (j2 + τ - 2)))
  have q1 := three_mul_le_of_real h1
  have q2 := three_mul_le_of_real h2
  have hP1' : ((T.drop (j1 - 1)).take (τ - 1)).HasPeriod (per (sub T j1 (j1 + τ - 2))) := by
    rw [← e1]
    exact hP1
  have hP2' : ((T.drop (j1 - 1 + (j2 - j1))).take (τ - 1)).HasPeriod
      (per (sub T j2 (j2 + τ - 2))) := by
    rw [← e2]
    exact hP2
  have hW := hasPeriod_glue2 T hp1 hp2 (by omega) (by omega) (by omega) hP1' hP2'
  have hQ : sub T j1 (j1 + τ - 1) = ((T.drop (j1 - 1)).take (j2 - j1 + (τ - 1))).take τ := by
    rw [List.take_take, Nat.min_eq_left (by omega)]
    exact sub_eq_window T hj1 (by omega)
  unfold InQ
  have hle : per (sub T j1 (j1 + τ - 1)) ≤ per (sub T j1 (j1 + τ - 2)) := by
    apply per_le_of_isPeriod
    rw [isPeriod_iff_hasPeriod, hQ]
    exact ⟨hp1, hW.infix (List.take_prefix _ _).isInfix⟩
  exact real_le_third_of_le (by omega)

/-- Two "left-type" boundary candidates `j₁ < j₂` close together force `j₂ ∈ Q`. -/
theorem inQ_of_two_left (T : List α) {τ j1 j2 : ℕ} (hj1 : 1 ≤ j1) (h12 : j1 < j2)
    (hd : 3 * (j2 - j1) + 1 ≤ τ) (hn : j2 + τ - 1 ≤ T.length)
    (h1 : (per (sub T (j1 + 1) (j1 + τ - 1)) : ℝ) ≤ (τ : ℝ) / 3)
    (h2 : (per (sub T (j2 + 1) (j2 + τ - 1)) : ℝ) ≤ (τ : ℝ) / 3) : InQ T τ j2 := by
  have hτ : 2 ≤ τ := by omega
  have e1 : sub T (j1 + 1) (j1 + τ - 1) = (T.drop j1).take (τ - 1) := by
    rw [show j1 + τ - 1 = j1 + 1 + (τ - 1) - 1 by omega, sub_eq_window T (by omega) (by omega),
      Nat.add_sub_cancel]
  have e2 : sub T (j2 + 1) (j2 + τ - 1) = (T.drop (j1 + (j2 - j1))).take (τ - 1) := by
    rw [show j2 + τ - 1 = j2 + 1 + (τ - 1) - 1 by omega, sub_eq_window T (by omega) (by omega),
      Nat.add_sub_cancel, show j1 + (j2 - j1) = j2 by omega]
  obtain ⟨hp1, hP1⟩ := (isPeriod_iff_hasPeriod _ _).1 (per_isPeriod (sub T (j1 + 1) (j1 + τ - 1)))
  obtain ⟨hp2, hP2⟩ := (isPeriod_iff_hasPeriod _ _).1 (per_isPeriod (sub T (j2 + 1) (j2 + τ - 1)))
  have q1 := three_mul_le_of_real h1
  have q2 := three_mul_le_of_real h2
  have hP1' : ((T.drop j1).take (τ - 1)).HasPeriod (per (sub T (j1 + 1) (j1 + τ - 1))) := by
    rw [← e1]
    exact hP1
  have hP2' : ((T.drop (j1 + (j2 - j1))).take (τ - 1)).HasPeriod
      (per (sub T (j2 + 1) (j2 + τ - 1))) := by
    rw [← e2]
    exact hP2
  have hW := hasPeriod_glue2 T hp1 hp2 (by omega) (by omega) (by omega) hP1' hP2'
  have hQ : sub T j2 (j2 + τ - 1) =
      (((T.drop j1).take (j2 - j1 + (τ - 1))).drop (j2 - j1 - 1)).take τ := by
    rw [window_window T (by omega), show j1 + (j2 - j1 - 1) = j2 - 1 by omega]
    exact sub_eq_window T (by omega) (by omega)
  unfold InQ
  have hle : per (sub T j2 (j2 + τ - 1)) ≤ per (sub T (j1 + 1) (j1 + τ - 1)) := by
    apply per_le_of_isPeriod
    rw [isPeriod_iff_hasPeriod, hQ]
    exact ⟨hp1, hW.infix (window_infix _ _ _)⟩
  exact real_le_third_of_le (by omega)

/-- **Local part of Lemma 8.8** of [KK19]: a block `[s..s+d]` of consecutive positions with
`3d + 1 ≤ τ`, inside `[1..n − τ + 1]`, contains at most two positions of `B`. -/
theorem card_inB_block_le_two (T : List α) {τ s d : ℕ} (hs : 1 ≤ s) (hd : 3 * d + 1 ≤ τ)
    (hn : s + d + τ - 1 ≤ T.length) [DecidablePred (InB T τ)] :
    ((Finset.Icc s (s + d)).filter (InB T τ)).card ≤ 2 := by
  classical
  let Rt : ℕ → Prop := fun j => ¬ InQ T τ j ∧ (per (sub T j (j + τ - 2)) : ℝ) ≤ (τ : ℝ) / 3
  let Lt : ℕ → Prop := fun j => ¬ InQ T τ j ∧ (per (sub T (j + 1) (j + τ - 1)) : ℝ) ≤ (τ : ℝ) / 3
  have hsub : (Finset.Icc s (s + d)).filter (InB T τ) ⊆
      (Finset.Icc s (s + d)).filter Rt ∪ (Finset.Icc s (s + d)).filter Lt := by
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    rcases hj.2.2 with h | h
    · exact Or.inl ⟨hj.1, hj.2.1, h⟩
    · exact Or.inr ⟨hj.1, hj.2.1, h⟩
  have hR : ((Finset.Icc s (s + d)).filter Rt).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter, Finset.mem_Icc] at hx hy
    by_contra hxy
    rcases lt_or_gt_of_ne hxy with h | h
    · exact hx.2.1 (inQ_of_two_right T (by omega) h (by omega) (by omega) hx.2.2 hy.2.2)
    · exact hy.2.1 (inQ_of_two_right T (by omega) h (by omega) (by omega) hy.2.2 hx.2.2)
  have hL : ((Finset.Icc s (s + d)).filter Lt).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    rw [Finset.mem_filter, Finset.mem_Icc] at hx hy
    by_contra hxy
    rcases lt_or_gt_of_ne hxy with h | h
    · exact hy.2.1 (inQ_of_two_left T (by omega) h (by omega) (by omega) hx.2.2 hy.2.2)
    · exact hx.2.1 (inQ_of_two_left T (by omega) h (by omega) (by omega) hy.2.2 hx.2.2)
  calc ((Finset.Icc s (s + d)).filter (InB T τ)).card
      ≤ ((Finset.Icc s (s + d)).filter Rt ∪ (Finset.Icc s (s + d)).filter Lt).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.Icc s (s + d)).filter Rt).card + ((Finset.Icc s (s + d)).filter Lt).card :=
        Finset.card_union_le _ _
    _ ≤ 2 := by omega

/-- **Boundary windows** (proof of Fact 8.9 of [KK19]): if the identifier gives every fragment at
a position of `B` a smaller value than every fragment at a position outside `B ∪ Q`, then a
synchronizing position `x` whose window `[x..x+τ]` meets `B` has `x ∈ B` or `x + τ ∈ B`. -/
theorem inB_of_sync_of_window_meets_B (T : List α) (τ : ℕ) (f : List α → ℕ)
    (hf : ∀ j k, InB T τ j → ¬ InB T τ k → ¬ InQ T τ k →
      f (sub T j (j + τ - 1)) < f (sub T k (k + τ - 1)))
    {x : ℕ} (hx : x ∈ syncSet T τ f) (hb : ∃ b, x ≤ b ∧ b ≤ x + τ ∧ InB T τ b) :
    InB T τ x ∨ InB T τ (x + τ) := by
  classical
  obtain ⟨b, hb1, hb2, hbB⟩ := hb
  unfold syncSet at hx
  rw [Finset.mem_filter] at hx
  rcases hx.2 with ⟨hnq, hmin⟩ | ⟨hnq, hmin⟩
  · left
    by_contra hxB
    have h1 := hf b x hbB hxB hnq
    have h2 := hmin b (Finset.mem_Icc.2 ⟨hb1, hb2⟩) hbB.1
    omega
  · right
    by_contra hxB
    have h1 := hf b (x + τ) hbB hxB hnq
    have h2 := hmin b (Finset.mem_Icc.2 ⟨hb1, hb2⟩) hbB.1
    rw [show x + τ + τ - 1 = x + 2 * τ - 1 by omega] at h1
    omega

end DynLZ77.Main.Aux

/-! ### Orderings: how often a given element is the minimum of a set -/

namespace DynLZ77.Main.Aux

open Finset

/-- Over all `N!` orderings `π` of `Fin N`, an element `a` of a set `A` is the `π`-minimum of `A`
for exactly `N!/|A|` of them: swapping `a` with another `a' ∈ A` is a bijection between the two
events, and the events for `a ∈ A` partition all orderings. -/
theorem card_argmin_mul (N : ℕ) (A : Finset (Fin N)) {a : Fin N} (ha : a ∈ A) :
    (univ.filter (fun π : Equiv.Perm (Fin N) => ∀ b ∈ A, π a ≤ π b)).card * A.card =
      N.factorial := by
  classical
  let P : Fin N → Finset (Equiv.Perm (Fin N)) :=
    fun c => univ.filter (fun π : Equiv.Perm (Fin N) => ∀ b ∈ A, π c ≤ π b)
  have hmemP : ∀ c π, π ∈ P c ↔ ∀ b ∈ A, π c ≤ π b := by
    intro c π
    simp only [P, mem_filter, mem_univ, true_and]
  have hswapA : ∀ a' ∈ A, ∀ b ∈ A, Equiv.swap a a' b ∈ A := by
    intro a' ha' b hb
    rcases eq_or_ne b a with rfl | h1
    · rw [Equiv.swap_apply_left]
      exact ha'
    · rcases eq_or_ne b a' with rfl | h2
      · rw [Equiv.swap_apply_right]
        exact ha
      · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
        exact hb
  -- all the events have the same size
  have hsame : ∀ a' ∈ A, (P a').card = (P a).card := by
    intro a' ha'
    apply Finset.card_bij (fun π _ => π * Equiv.swap a a')
    · intro π hπ
      rw [hmemP] at hπ ⊢
      intro b hb
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      exact hπ _ (hswapA a' ha' b hb)
    · intro π₁ _ π₂ _ h
      exact mul_right_cancel h
    · intro σ hσ
      refine ⟨σ * Equiv.swap a a', ?_, ?_⟩
      · rw [hmemP] at hσ ⊢
        intro b hb
        rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
        exact hσ _ (hswapA a' ha' b hb)
      · rw [mul_assoc, Equiv.swap_mul_self, mul_one]
  -- the events partition all orderings
  have hcover : (univ : Finset (Equiv.Perm (Fin N))) = A.biUnion P := by
    ext π
    simp only [mem_univ, true_iff, mem_biUnion]
    obtain ⟨m, hm, hmin⟩ := A.exists_min_image (fun b => π b) ⟨a, ha⟩
    exact ⟨m, hm, (hmemP m π).2 hmin⟩
  have hdisj : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → Disjoint (P x) (P y) := by
    intro x hx y hy hxy
    rw [Finset.disjoint_left]
    intro π h1 h2
    rw [hmemP] at h1 h2
    exact hxy (π.injective (le_antisymm (h1 y hy) (h2 x hx)))
  have hcard : N.factorial = ∑ c ∈ A, (P c).card := by
    rw [← Finset.card_biUnion hdisj, ← hcover, Finset.card_univ, Fintype.card_perm,
      Fintype.card_fin]
  rw [hcard, Finset.sum_congr rfl hsame, Finset.sum_const, smul_eq_mul, mul_comm]

/-- **Averaging over orderings.** Positions `x ∈ X` each come with a set `A x` of at least
`(τ+1)/3` items and two items `u x, v x ∈ A x`; position `x` is *selected* by an ordering `π` when
`u x` or `v x` is the `π`-minimum of `A x`. Some ordering selects at most `6|X|/(τ+1)` positions. -/
theorem exists_good_perm (N : ℕ) (X : Finset ℕ) (τ : ℕ) (A : ℕ → Finset (Fin N))
    (u v : ℕ → Fin N) (hu : ∀ x ∈ X, u x ∈ A x) (hv : ∀ x ∈ X, v x ∈ A x)
    (hA : ∀ x ∈ X, τ + 1 ≤ 3 * (A x).card) :
    ∃ π : Equiv.Perm (Fin N),
      (X.filter (fun x => (∀ b ∈ A x, π (u x) ≤ π b) ∨ (∀ b ∈ A x, π (v x) ≤ π b))).card *
        (τ + 1) ≤ 6 * X.card := by
  classical
  have hper : ∀ x ∈ X, (univ.filter (fun π : Equiv.Perm (Fin N) =>
      (∀ b ∈ A x, π (u x) ≤ π b) ∨ (∀ b ∈ A x, π (v x) ≤ π b))).card * (τ + 1) ≤
        6 * N.factorial := by
    intro x hx
    have h1 := card_argmin_mul N (A x) (hu x hx)
    have h2 := card_argmin_mul N (A x) (hv x hx)
    have hle : (univ.filter (fun π : Equiv.Perm (Fin N) =>
        (∀ b ∈ A x, π (u x) ≤ π b) ∨ (∀ b ∈ A x, π (v x) ≤ π b))).card ≤
        (univ.filter (fun π : Equiv.Perm (Fin N) => ∀ b ∈ A x, π (u x) ≤ π b)).card +
        (univ.filter (fun π : Equiv.Perm (Fin N) => ∀ b ∈ A x, π (v x) ≤ π b)).card := by
      rw [Finset.filter_or]
      exact Finset.card_union_le _ _
    have h3 := hA x hx
    calc _ ≤ ((univ.filter (fun π : Equiv.Perm (Fin N) => ∀ b ∈ A x, π (u x) ≤ π b)).card +
          (univ.filter (fun π : Equiv.Perm (Fin N) => ∀ b ∈ A x, π (v x) ≤ π b)).card) *
            (τ + 1) := Nat.mul_le_mul_right _ hle
      _ ≤ ((univ.filter (fun π : Equiv.Perm (Fin N) => ∀ b ∈ A x, π (u x) ≤ π b)).card +
          (univ.filter (fun π : Equiv.Perm (Fin N) => ∀ b ∈ A x, π (v x) ≤ π b)).card) *
            (3 * (A x).card) := Nat.mul_le_mul_left _ h3
      _ = 3 * ((univ.filter (fun π : Equiv.Perm (Fin N) => ∀ b ∈ A x, π (u x) ≤ π b)).card *
            (A x).card) +
          3 * ((univ.filter (fun π : Equiv.Perm (Fin N) => ∀ b ∈ A x, π (v x) ≤ π b)).card *
            (A x).card) := by ring
      _ = 6 * N.factorial := by rw [h1, h2]; ring
  have hsum : ∑ π : Equiv.Perm (Fin N),
      (X.filter (fun x => (∀ b ∈ A x, π (u x) ≤ π b) ∨ (∀ b ∈ A x, π (v x) ≤ π b))).card *
        (τ + 1) ≤ ∑ _π : Equiv.Perm (Fin N), 6 * X.card := by
    calc _ = ∑ x ∈ X, (univ.filter (fun π : Equiv.Perm (Fin N) =>
          (∀ b ∈ A x, π (u x) ≤ π b) ∨ (∀ b ∈ A x, π (v x) ≤ π b))).card * (τ + 1) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          congr 1
          simp only [Finset.card_filter]
          exact Finset.sum_comm
      _ ≤ ∑ _x ∈ X, 6 * N.factorial := Finset.sum_le_sum hper
      _ = ∑ _π : Equiv.Perm (Fin N), 6 * X.card := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
            Fintype.card_fin, smul_eq_mul, smul_eq_mul]
          ring
  obtain ⟨π, -, hπ⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨π, hπ⟩

variable {α : Type}

open DynLZ77.KK in
/-- A window `[x..x+τ]` free of `Q` contains at least `(τ+1)/3` distinct length-`τ` fragments:
by Fact 8.3 equal fragments there are more than `τ/3` apart, so each occurs at most 3 times. -/
theorem card_image_frags (T : List α) [DecidableEq α] {τ x : ℕ} (hx : 1 ≤ x)
    (hclean : ∀ y, x ≤ y → y ≤ x + τ → ¬ InQ T τ y) :
    τ + 1 ≤ 3 * ((Finset.Icc x (x + τ)).image (fun y => sub T y (y + τ - 1))).card := by
  have hcard : (Finset.Icc x (x + τ)).card = τ + 1 := by
    rw [Nat.card_Icc]
    omega
  rw [← hcard]
  apply Finset.card_le_mul_card_image
  intro w _
  have hfar : ∀ p ∈ (Finset.Icc x (x + τ)).filter (fun y => sub T y (y + τ - 1) = w),
      ∀ p' ∈ (Finset.Icc x (x + τ)).filter (fun y => sub T y (y + τ - 1) = w),
      p < p' → τ < 3 * (p' - p) := by
    intro p hp p' hp' hlt
    rw [Finset.mem_filter, Finset.mem_Icc] at hp hp'
    by_contra hle
    exact hclean p hp.1.1 hp.1.2
      (inQ_of_close_repeat T (by omega) hlt (by omega) (hp.2.trans hp'.2.symm))
  by_contra hF
  set F := (Finset.Icc x (x + τ)).filter (fun y => sub T y (y + τ - 1) = w) with hFdef
  have hF' : 3 < F.card := by omega
  have hne : F.Nonempty := Finset.card_pos.1 (by omega)
  have hmM : F.min' hne < F.max' hne := Finset.min'_lt_max'_of_card F (by omega)
  have hm := F.min'_mem hne
  have hM := F.max'_mem hne
  have hM' : F.max' hne ∈ F.erase (F.min' hne) := Finset.mem_erase.2 ⟨hmM.ne', hM⟩
  have h2 : 1 < ((F.erase (F.min' hne)).erase (F.max' hne)).card := by
    rw [Finset.card_erase_of_mem hM', Finset.card_erase_of_mem hm]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h2
  simp only [Finset.mem_erase] at ha hb
  have hmin_a := F.min'_le a ha.2.2
  have hmin_b := F.min'_le b hb.2.2
  have hmax_a := F.le_max' a ha.2.2
  have hmax_b := F.le_max' b hb.2.2
  have hmw : F.min' hne ∈ Finset.Icc x (x + τ) := (Finset.mem_filter.1 hm).1
  have hMw : F.max' hne ∈ Finset.Icc x (x + τ) := (Finset.mem_filter.1 hM).1
  rw [Finset.mem_Icc] at hmw hMw
  rcases lt_or_gt_of_ne hab with h | h
  · have g1 := hfar _ hm a ha.2.2 (lt_of_le_of_ne hmin_a (Ne.symm ha.2.1))
    have g2 := hfar a ha.2.2 b hb.2.2 h
    have g3 := hfar b hb.2.2 _ hM (lt_of_le_of_ne hmax_b hb.1)
    omega
  · have g1 := hfar _ hm b hb.2.2 (lt_of_le_of_ne hmin_b (Ne.symm hb.2.1))
    have g2 := hfar b hb.2.2 a ha.2.2 h
    have g3 := hfar a ha.2.2 _ hM (lt_of_le_of_ne hmax_a ha.1)
    omega

end DynLZ77.Main.Aux
/-! ## Assembly: the localized size bound -/

namespace DynLZ77.Main.Aux

open DynLZ77.KK

variable {α : Type}

/-- Membership in `B` depends only on the fragment `T[j..j+τ)`. -/
theorem inB_iff_frag (T : List α) {τ j : ℕ} (hj : 1 ≤ j) (hτ : 1 ≤ τ) :
    InB T τ j ↔ (¬ ((per (sub T j (j + τ - 1)) : ℝ) ≤ (τ : ℝ) / 3) ∧
      (((per ((sub T j (j + τ - 1)).take (τ - 1)) : ℝ) ≤ (τ : ℝ) / 3) ∨
        ((per ((sub T j (j + τ - 1)).drop 1) : ℝ) ≤ (τ : ℝ) / 3))) := by
  have e0 : sub T j (j + τ - 1) = (T.drop (j - 1)).take τ := sub_eq_window T hj hτ
  have e1 : sub T j (j + τ - 2) = (sub T j (j + τ - 1)).take (τ - 1) := by
    rw [e0, List.take_take, Nat.min_eq_left (by omega)]
    unfold sub
    rw [show j + τ - 2 + 1 - j = τ - 1 by omega]
  have e2 : sub T (j + 1) (j + τ - 1) = (sub T j (j + τ - 1)).drop 1 := by
    rw [e0, List.drop_take, List.drop_drop]
    unfold sub
    rw [show j + τ - 1 + 1 - (j + 1) = τ - 1 by omega, show j + 1 - 1 = j - 1 + 1 by omega]
  unfold InB InQ
  rw [e1, e2]

theorem inB_congr (T : List α) {τ j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) (hτ : 1 ≤ τ)
    (h : sub T j (j + τ - 1) = sub T k (k + τ - 1)) : InB T τ j ↔ InB T τ k := by
  rw [inB_iff_frag T hj hτ, inB_iff_frag T hk hτ, h]

theorem not_inQ_of_le_two (T : List α) {τ y : ℕ} (hτ : τ ≤ 2) : ¬ InQ T τ y := by
  intro h
  have h1 := three_mul_le_of_real h
  have h2 := (per_isPeriod (sub T y (y + τ - 1))).1
  omega

open Classical in
/-- At most `2m` boundary positions (with their fragment inside `T`) in `m` consecutive blocks of
`d + 1` positions, `3d + 1 ≤ τ`. -/
theorem card_inB_blocks (T : List α) {τ d : ℕ} (hd : 3 * d + 1 ≤ τ) :
    ∀ m s, 1 ≤ s → ((Finset.Icc s (s + m * (d + 1) - 1)).filter
      (fun y => y + τ - 1 ≤ T.length ∧ InB T τ y)).card ≤ 2 * m := by
  classical
  intro m
  induction m with
  | zero =>
    intro s hs
    have : (Finset.Icc s (s + 0 * (d + 1) - 1)) = ∅ := by
      rw [Finset.Icc_eq_empty_iff]
      omega
    rw [this]
    simp
  | succ m ih =>
    intro s hs
    have hsplit : (Finset.Icc s (s + (m + 1) * (d + 1) - 1)).filter
        (fun y => y + τ - 1 ≤ T.length ∧ InB T τ y) ⊆
        (Finset.Icc s (s + d)).filter (fun y => y + τ - 1 ≤ T.length ∧ InB T τ y) ∪
        (Finset.Icc (s + (d + 1)) (s + (d + 1) + m * (d + 1) - 1)).filter
          (fun y => y + τ - 1 ≤ T.length ∧ InB T τ y) := by
      intro y hy
      rw [Finset.mem_filter, Finset.mem_Icc, Nat.succ_mul] at hy
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
      by_cases hyd : y ≤ s + d
      · exact Or.inl ⟨⟨hy.1.1, hyd⟩, hy.2⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩, hy.2⟩
    have h1 : ((Finset.Icc s (s + d)).filter
        (fun y => y + τ - 1 ≤ T.length ∧ InB T τ y)).card ≤ 2 := by
      by_cases hfit : s + τ - 1 ≤ T.length
      · have hsub : (Finset.Icc s (s + d)).filter (fun y => y + τ - 1 ≤ T.length ∧ InB T τ y) ⊆
            (Finset.Icc s (s + min d (T.length + 1 - τ - s))).filter (InB T τ) := by
          intro y hy
          rw [Finset.mem_filter, Finset.mem_Icc] at hy ⊢
          exact ⟨⟨hy.1.1, by omega⟩, hy.2.2⟩
        exact (Finset.card_le_card hsub).trans
          (card_inB_block_le_two T hs (by omega) (by omega))
      · have hempty : (Finset.Icc s (s + d)).filter
            (fun y => y + τ - 1 ≤ T.length ∧ InB T τ y) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro y hy h
          rw [Finset.mem_Icc] at hy
          omega
        rw [hempty]
        simp
    have h2 := ih (s + (d + 1)) (by omega)
    calc _ ≤ _ := Finset.card_le_card hsplit
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ 2 + 2 * m := Nat.add_le_add h1 h2
      _ = 2 * (m + 1) := by ring

open Classical in
/-- Boundary positions within `[i − 11τ .. i + 12τ]` of some `i ∈ I` number at most `140·|I|`. -/
theorem card_inB_near (T : List α) (I : Finset ℕ) {τ : ℕ} (hτ : 1 ≤ τ) :
    ((Finset.Icc 1 (T.length + 1 - τ)).filter
      (fun y => InB T τ y ∧ ∃ i ∈ I, i ≤ y + 11 * τ ∧ y ≤ i + 12 * τ)).card ≤ 140 * I.card := by
  classical
  have hd : 3 * ((τ - 1) / 3) + 1 ≤ τ := by omega
  have hsub : (Finset.Icc 1 (T.length + 1 - τ)).filter
      (fun y => InB T τ y ∧ ∃ i ∈ I, i ≤ y + 11 * τ ∧ y ≤ i + 12 * τ) ⊆
      I.biUnion (fun i => (Finset.Icc (max 1 (i - 11 * τ))
        (max 1 (i - 11 * τ) + 70 * ((τ - 1) / 3 + 1) - 1)).filter
          (fun y => y + τ - 1 ≤ T.length ∧ InB T τ y)) := by
    intro y hy
    rw [Finset.mem_filter, Finset.mem_Icc] at hy
    obtain ⟨⟨hy1, hy2⟩, hB, i, hi, hi1, hi2⟩ := hy
    rw [Finset.mem_biUnion]
    refine ⟨i, hi, ?_⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, by omega, hB⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ I, ((Finset.Icc (max 1 (i - 11 * τ))
          (max 1 (i - 11 * τ) + 70 * ((τ - 1) / 3 + 1) - 1)).filter
            (fun y => y + τ - 1 ≤ T.length ∧ InB T τ y)).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, 2 * 70 := Finset.sum_le_sum (fun i _ =>
          card_inB_blocks T hd 70 _ (le_max_left _ _))
    _ = 140 * I.card := by rw [Finset.sum_const, smul_eq_mul]; ring

/-- The boundary-window rule with the identifier condition required only for positions whose
fragment lies inside `T`. -/
theorem inB_of_sync_of_window_meets_B' (T : List α) (τ : ℕ) (f : List α → ℕ)
    (hf : ∀ j k, 1 ≤ j → j + τ - 1 ≤ T.length → 1 ≤ k → k + τ - 1 ≤ T.length →
      InB T τ j → ¬ InB T τ k → ¬ InQ T τ k →
      f (sub T j (j + τ - 1)) < f (sub T k (k + τ - 1)))
    {x : ℕ} (hx : x ∈ syncSet T τ f) (hb : ∃ b, x ≤ b ∧ b ≤ x + τ ∧ InB T τ b) :
    InB T τ x ∨ InB T τ (x + τ) := by
  classical
  obtain ⟨b, hb1, hb2, hbB⟩ := hb
  unfold syncSet at hx
  rw [Finset.mem_filter, Finset.mem_Icc] at hx
  obtain ⟨⟨hx1, hx2⟩, hx⟩ := hx
  rcases hx with ⟨hnq, hmin⟩ | ⟨hnq, hmin⟩
  · left
    by_contra hxB
    have h1 := hf b x (by omega) (by omega) hx1 (by omega) hbB hxB hnq
    have h2 := hmin b (Finset.mem_Icc.2 ⟨hb1, hb2⟩) hbB.1
    omega
  · right
    by_contra hxB
    have h1 := hf b (x + τ) (by omega) (by omega) (by omega) (by omega) hbB hxB hnq
    have h2 := hmin b (Finset.mem_Icc.2 ⟨hb1, hb2⟩) hbB.1
    rw [show x + τ + τ - 1 = x + 2 * τ - 1 by omega] at h1
    omega

/-- **The localized size bound** for Construction 8.1 (Fact 8.9 of [KK19], localized), with
`C = 412`. -/
theorem local_sparse_main : ∃ C : ℝ, ∀ {α : Type} [DecidableEq α] (T : List α) (I : Finset ℕ)
    (τ : ℕ), I ⊆ Finset.Icc 1 T.length → 1 ≤ τ → τ ≤ T.length / 2 →
      ∃ id : List α → ℕ,
        (((syncSet T τ id).filter (fun x => ∃ i ∈ I, i ≤ x + 11 * τ ∧ x ≤ i + 11 * τ)).card : ℝ)
          ≤ C * (I.card : ℝ) := by
  refine ⟨412, fun {α} _ T I τ hI hτ1 hτn => ?_⟩
  classical
  -- the fragments at clean positions, and an injective ranking space for them
  obtain ⟨U, hU⟩ : ∃ U : Finset (List α), U = ((Finset.Icc 1 (T.length + 1 - τ)).filter
      (fun y => ¬ InQ T τ y ∧ ¬ InB T τ y)).image (fun y => sub T y (y + τ - 1)) := ⟨_, rfl⟩
  have hmemU : ∀ y, 1 ≤ y → y + τ - 1 ≤ T.length → ¬ InQ T τ y → ¬ InB T τ y →
      sub T y (y + τ - 1) ∈ U := by
    intro y h1 h2 h3 h4
    rw [hU]
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨h1, by omega⟩, h3, h4⟩)
  obtain ⟨g, hg⟩ : ∃ g : List α → Fin (U.card + 1),
      ∀ w ∈ U, ∀ w' ∈ U, g w = g w' → w = w' := by
    refine ⟨fun w => if h : w ∈ U then (U.equivFin ⟨w, h⟩).castSucc else Fin.last U.card, ?_⟩
    intro w hw w' hw' h
    simp only [dif_pos hw, dif_pos hw'] at h
    exact congrArg Subtype.val (U.equivFin.injective (Fin.castSucc_injective _ h))
  -- the clean positions near `I`
  obtain ⟨X, hX⟩ : ∃ X : Finset ℕ, X = (Finset.Icc 1 (T.length + 1 - 2 * τ)).filter
      (fun x => (∃ i ∈ I, i ≤ x + 11 * τ ∧ x ≤ i + 11 * τ) ∧
        ∀ y ∈ Finset.Icc x (x + τ), ¬ InQ T τ y ∧ ¬ InB T τ y) := ⟨_, rfl⟩
  have hu : ∀ x ∈ X, g (sub T x (x + τ - 1)) ∈
      (Finset.Icc x (x + τ)).image (fun y => g (sub T y (y + τ - 1))) :=
    fun x _ => Finset.mem_image_of_mem _ (Finset.mem_Icc.2 ⟨le_rfl, by omega⟩)
  have hv : ∀ x ∈ X, g (sub T (x + τ) (x + τ + τ - 1)) ∈
      (Finset.Icc x (x + τ)).image (fun y => g (sub T y (y + τ - 1))) :=
    fun x _ => Finset.mem_image_of_mem (fun y => g (sub T y (y + τ - 1)))
      (Finset.mem_Icc.2 ⟨by omega, le_rfl⟩)
  have hA : ∀ x ∈ X, τ + 1 ≤
      3 * ((Finset.Icc x (x + τ)).image (fun y => g (sub T y (y + τ - 1)))).card := by
    intro x hx
    rw [hX, Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨hx1, hx2⟩, _, hcl⟩ := hx
    have hinU : ∀ y ∈ Finset.Icc x (x + τ), sub T y (y + τ - 1) ∈ U := by
      intro y hy
      have hy' := Finset.mem_Icc.1 hy
      exact hmemU y (by omega) (by omega) (hcl y hy).1 (hcl y hy).2
    have himg : (Finset.Icc x (x + τ)).image (fun y => g (sub T y (y + τ - 1))) =
        ((Finset.Icc x (x + τ)).image (fun y => sub T y (y + τ - 1))).image g := by
      rw [Finset.image_image]
      rfl
    have hcard : ((Finset.Icc x (x + τ)).image (fun y => g (sub T y (y + τ - 1)))).card =
        ((Finset.Icc x (x + τ)).image (fun y => sub T y (y + τ - 1))).card := by
      rw [himg]
      apply Finset.card_image_of_injOn
      intro w hw w' hw' h
      rw [Finset.mem_coe, Finset.mem_image] at hw hw'
      obtain ⟨y, hy, rfl⟩ := hw
      obtain ⟨y', hy', rfl⟩ := hw'
      exact hg _ (hinU y hy) _ (hinU y' hy') h
    rw [hcard]
    exact card_image_frags T hx1 (fun y h1 h2 => (hcl y (Finset.mem_Icc.2 ⟨h1, h2⟩)).1)
  -- an ordering selecting few clean positions
  obtain ⟨π, hπ⟩ := exists_good_perm (U.card + 1) X τ
    (fun x => (Finset.Icc x (x + τ)).image (fun y => g (sub T y (y + τ - 1))))
    (fun x => g (sub T x (x + τ - 1))) (fun x => g (sub T (x + τ) (x + τ + τ - 1))) hu hv hA
  obtain ⟨sel, hsel, hselπ⟩ : ∃ sel : Finset ℕ, sel = X.filter (fun x =>
      (∀ b ∈ (Finset.Icc x (x + τ)).image (fun y => g (sub T y (y + τ - 1))),
        π (g (sub T x (x + τ - 1))) ≤ π b) ∨
      (∀ b ∈ (Finset.Icc x (x + τ)).image (fun y => g (sub T y (y + τ - 1))),
        π (g (sub T (x + τ) (x + τ + τ - 1))) ≤ π b)) ∧ sel.card * (τ + 1) ≤ 6 * X.card :=
    ⟨_, rfl, hπ⟩
  -- the identifier: boundary fragments first (value 0), then clean fragments ranked by `π`
  obtain ⟨f, hfdef⟩ : ∃ f : List α → ℕ, ∀ w, f w = if w ∈ U then 1 + (π (g w) : ℕ) else 0 :=
    ⟨_, fun w => rfl⟩
  have hf : ∀ j k, 1 ≤ j → j + τ - 1 ≤ T.length → 1 ≤ k → k + τ - 1 ≤ T.length →
      InB T τ j → ¬ InB T τ k → ¬ InQ T τ k →
      f (sub T j (j + τ - 1)) < f (sub T k (k + τ - 1)) := by
    intro j k hj1 hj2 hk1 hk2 hjB hkB hkQ
    have hk : sub T k (k + τ - 1) ∈ U := hmemU k hk1 hk2 hkQ hkB
    have hj : sub T j (j + τ - 1) ∉ U := by
      intro hjU
      rw [hU, Finset.mem_image] at hjU
      obtain ⟨k', hk', heq⟩ := hjU
      rw [Finset.mem_filter, Finset.mem_Icc] at hk'
      exact hk'.2.2 ((inB_congr T (by omega) hj1 hτ1 heq).2 hjB)
    rw [hfdef, hfdef, if_neg hj, if_pos hk]
    omega
  refine ⟨f, ?_⟩
  -- boundary positions near `I`
  obtain ⟨Bn, hBn⟩ : ∃ Bn : Finset ℕ, Bn = (Finset.Icc 1 (T.length + 1 - τ)).filter
      (fun y => InB T τ y ∧ ∃ i ∈ I, i ≤ y + 11 * τ ∧ y ≤ i + 12 * τ) := ⟨_, rfl⟩
  have hBcard : Bn.card ≤ 140 * I.card := by
    rw [hBn]
    exact card_inB_near T I hτ1
  -- every synchronizing position near `I` is a boundary position, `τ` before one, or selected
  have hsub : (syncSet T τ f).filter (fun x => ∃ i ∈ I, i ≤ x + 11 * τ ∧ x ≤ i + 11 * τ) ⊆
      Bn ∪ Bn.image (fun y => y - τ) ∪ sel := by
    intro x hx
    rw [Finset.mem_filter] at hx
    obtain ⟨hxS, hnear⟩ := hx
    have hxS' := hxS
    unfold syncSet at hxS'
    rw [Finset.mem_filter, Finset.mem_Icc] at hxS'
    obtain ⟨⟨hx1, hx2⟩, hpred⟩ := hxS'
    rw [Finset.mem_union, Finset.mem_union]
    by_cases hb : ∃ b, x ≤ b ∧ b ≤ x + τ ∧ InB T τ b
    · obtain ⟨i, hi, hi1, hi2⟩ := hnear
      rcases inB_of_sync_of_window_meets_B' T τ f hf hxS hb with h | h
      · left; left
        rw [hBn, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hx1, by omega⟩, h, i, hi, hi1, by omega⟩
      · left; right
        rw [Finset.mem_image]
        refine ⟨x + τ, ?_, by omega⟩
        rw [hBn, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨by omega, by omega⟩, h, i, hi, by omega, by omega⟩
    · right
      have hnoB : ∀ y, x ≤ y → y ≤ x + τ → ¬ InB T τ y :=
        fun y h1 h2 hB => hb ⟨y, h1, h2, hB⟩
      have hnoQ : ∀ y, x ≤ y → y ≤ x + τ → ¬ InQ T τ y := by
        by_cases hτ2 : τ ≤ 2
        · exact fun y _ _ => not_inQ_of_le_two T hτ2
        · intro y hy1 hy2 hyQ
          have hsome : ∃ b, x ≤ b ∧ b ≤ x + τ ∧ ¬ InQ T τ b := by
            rcases hpred with ⟨hq, _⟩ | ⟨hq, _⟩
            · exact ⟨x, le_rfl, by omega, hq⟩
            · exact ⟨x + τ, by omega, le_rfl, hq⟩
          obtain ⟨c, hc1, hc2, hcB⟩ := exists_inB T (by omega) hx1 ⟨y, hy1, hy2, hyQ⟩ hsome
          exact hnoB c hc1 hc2 hcB
      have hfU : ∀ y, x ≤ y → y ≤ x + τ →
          f (sub T y (y + τ - 1)) = 1 + (π (g (sub T y (y + τ - 1))) : ℕ) := by
        intro y h1 h2
        rw [hfdef, if_pos (hmemU y (by omega) (by omega) (hnoQ y h1 h2) (hnoB y h1 h2))]
      rw [hsel, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [hX, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨hx1, hx2⟩, hnear, fun y hy =>
          ⟨hnoQ y (Finset.mem_Icc.1 hy).1 (Finset.mem_Icc.1 hy).2,
            hnoB y (Finset.mem_Icc.1 hy).1 (Finset.mem_Icc.1 hy).2⟩⟩
      · rcases hpred with ⟨_, hmin⟩ | ⟨_, hmin⟩
        · left
          intro b hb'
          rw [Finset.mem_image] at hb'
          obtain ⟨y, hy, rfl⟩ := hb'
          have hy' := Finset.mem_Icc.1 hy
          have h := hmin y hy (hnoQ y hy'.1 hy'.2)
          rw [hfU x le_rfl (by omega), hfU y hy'.1 hy'.2] at h
          exact Fin.le_iff_val_le_val.2 (by omega)
        · right
          intro b hb'
          rw [Finset.mem_image] at hb'
          obtain ⟨y, hy, rfl⟩ := hb'
          have hy' := Finset.mem_Icc.1 hy
          have h := hmin y hy (hnoQ y hy'.1 hy'.2)
          rw [show x + 2 * τ - 1 = x + τ + τ - 1 by omega, hfU (x + τ) (by omega) le_rfl,
            hfU y hy'.1 hy'.2] at h
          exact Fin.le_iff_val_le_val.2 (by omega)
  -- counting
  have hXcard : X.card ≤ (22 * τ + 1) * I.card := by
    have hXsub : X ⊆ I.biUnion (fun i => Finset.Icc (i - 11 * τ) (i + 11 * τ)) := by
      intro x hx
      rw [hX, Finset.mem_filter] at hx
      obtain ⟨i, hi, h1, h2⟩ := hx.2.1
      rw [Finset.mem_biUnion]
      exact ⟨i, hi, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩
    calc X.card ≤ _ := Finset.card_le_card hXsub
      _ ≤ ∑ i ∈ I, (Finset.Icc (i - 11 * τ) (i + 11 * τ)).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ I, (22 * τ + 1) :=
          Finset.sum_le_sum (fun i _ => by rw [Nat.card_Icc]; omega)
      _ = (22 * τ + 1) * I.card := by rw [Finset.sum_const, smul_eq_mul]; ring
  have hselc : sel.card ≤ 132 * I.card := by
    have h1 : sel.card * (τ + 1) ≤ 132 * I.card * (τ + 1) := by
      calc sel.card * (τ + 1) ≤ 6 * X.card := hselπ
        _ ≤ 6 * ((22 * τ + 1) * I.card) := Nat.mul_le_mul_left _ hXcard
        _ = (132 * τ + 6) * I.card := by ring
        _ ≤ (132 * τ + 132) * I.card := Nat.mul_le_mul_right _ (by omega)
        _ = 132 * I.card * (τ + 1) := by ring
    exact Nat.le_of_mul_le_mul_right h1 (by omega)
  have hcount : ((syncSet T τ f).filter
      (fun x => ∃ i ∈ I, i ≤ x + 11 * τ ∧ x ≤ i + 11 * τ)).card ≤ 412 * I.card := by
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (Bn ∪ Bn.image (fun y => y - τ)) sel
    have h3 := Finset.card_union_le Bn (Bn.image (fun y => y - τ))
    have h4 := Finset.card_image_le (s := Bn) (f := fun y => y - τ)
    omega
  exact_mod_cast hcount

end DynLZ77.Main.Aux
open DynLZ77.Main DynLZ77.KK

/-- **Sparse identifiers, localized** ([KK19, Construction 8.1 and Fact 8.9], localized to the
`11τ`-neighbourhood of a set `I`), with `C = 412`. -/
theorem solution : ∃ C : ℝ, ∀ {α : Type} [DecidableEq α] (T : List α) (I : Finset ℕ) (τ : ℕ),
    I ⊆ Finset.Icc 1 T.length → 1 ≤ τ → τ ≤ T.length / 2 →
      ∃ id : List α → ℕ,
        (((syncSet T τ id).filter (fun x => ∃ i ∈ I, i ≤ x + 11 * τ ∧ x ≤ i + 11 * τ)).card : ℝ)
          ≤ C * (I.card : ℝ) :=
  DynLZ77.Main.Aux.local_sparse_main
