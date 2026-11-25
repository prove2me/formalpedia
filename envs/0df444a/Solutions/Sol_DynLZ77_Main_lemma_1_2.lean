-- Prove2me | solution 1 for DynLZ77.Main.lemma_1_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shaygo
-- created : 2026-11-25T09:06:15.641796+00:00
-- url     : https://prove2.me/submissions/b96771e9-8ed0-42f7-9ccb-59ba736a7648
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.List.PeriodicityLemma
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_DynLZ77_KK_SyncConstruction
import Definitions.Def_DynLZ77_Main_ExtensionPoints
import Theorems.Thm_DynLZ77_Main_lemma_2_2
import Theorems.Thm_DynLZ77_Main_lemma_1_2_per
import Theorems.Thm_DynLZ77_Main_lemma_8_4
import Theorems.Thm_DynLZ77_Main_lemma_8_8
import Theorems.Thm_DynLZ77_Main_fact_8_9
import Theorems.Thm_DynLZ77_Main_claim_8_10
import Theorems.Thm_DynLZ77_Main_claim_8_11
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

/-! ## Lemma 1.2: bounding Ired_Aper (pp. 51–52) and assembling the bound -/

namespace DynLZ77.Main.Aux

variable {α : Type}

/-- A substring of a substring. -/
theorem sub_of_sub (S : List α) {a b c d : ℕ} (ha : 1 ≤ a) (hc : 1 ≤ c) (hcd : c ≤ d + 1)
    (hd : d ≤ b + 1 - a) : sub (sub S a b) c d = sub S (a + c - 1) (a + d - 1) := by
  unfold sub
  rw [window_window S (by omega), show a + c - 1 - 1 = a - 1 + (c - 1) by omega,
    show a + d - 1 + 1 - (a + c - 1) = d + 1 - c by omega]

theorem length_sub_eq (S : List α) {a len : ℕ} (ha : 1 ≤ a) (hlen : a + len - 1 ≤ S.length)
    (h1 : 1 ≤ len) : (sub S a (a + len - 1)).length = len := by
  rw [sub_eq_window S ha h1, List.length_take, List.length_drop]
  omega

variable [DecidableEq α]

open Classical in
/-- **Core of "Bounding `Ired_Aper`"** (p. 51–52): for a dyadic class `2^k ≤ LPF′(i) < 2^{k+1}`
with `k ≥ 5`, `τ = ⌊2^k/3⌋ − 1` and a `Z`-local `τ`-synchronizing set `Sy`, every index `i` of the
class is `x + 1 − q.1` for some `x ∈ Sy ∩ [1..n]` and some non-dominated extension point
`q ∈ DExt_{Sy∩[1..n]}(x, S)` (namely `x = i + k′` and `q = (k′+1, ℓ−k′)`). -/
theorem aper_core (S : List α) {k : ℕ} (hk : 5 ≤ k) (Sy : Finset ℕ)
    (hsync : IsLocalSyncSet S ((LZ77 S).map Prod.fst).toFinset (2 ^ k / 3 - 1) Sy) :
    ∀ i ∈ (Ired S).filter
        (fun i => ¬ HighlyPeriodic (sub S i (i + lpf' S i - 1)) ∧ Nat.log 2 (lpf' S i) = k),
      ∃ x ∈ Sy.filter (fun a => 1 ≤ a ∧ a ≤ S.length),
        ∃ q ∈ dext S (Sy.filter (fun a => 1 ≤ a ∧ a ≤ S.length)) x, x + 1 - q.1 = i := by
  intro i hi
  rw [Finset.mem_filter] at hi
  obtain ⟨hiIred, hnp, hlog⟩ := hi
  have hiIred' := hiIred
  rw [Ired, Finset.mem_filter, Finset.mem_Icc] at hiIred'
  obtain ⟨⟨hi1, hin⟩, -⟩ := hiIred'
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = lpf' S i := ⟨_, rfl⟩
  rw [← hℓ] at hnp hlog
  -- the dyadic class
  have hℓ0 : ℓ ≠ 0 := by have := lt_add_lpf' S i; omega
  have hX1 : 2 ^ k ≤ ℓ := by rw [← hlog]; exact Nat.pow_log_le_self 2 hℓ0
  have hX2 : ℓ < 2 * 2 ^ k := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) ℓ
    rw [hlog, pow_succ] at this
    omega
  have hX : 32 ≤ 2 ^ k := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨X, hXdef⟩ : ∃ X, X = 2 ^ k := ⟨_, rfl⟩
  rw [← hXdef] at hX1 hX2 hX hsync
  obtain ⟨τ, hτ⟩ : ∃ τ, τ = X / 3 - 1 := ⟨_, rfl⟩
  rw [← hτ] at hsync
  have hiℓ : i + ℓ ≤ S.length + 1 := by rw [hℓ]; exact add_lpf'_le S hi1 hin
  -- `LPF(i) = ℓ ≥ 2`, so `S[i..i+ℓ)` occurs earlier; let `i′` be its leftmost occurrence
  have hlpf : lpf S i = ℓ := by
    have h1 : lpf' S i = max (lpf S i) 1 := rfl
    rw [← hℓ] at h1
    rcases le_total (lpf S i) 1 with h | h
    · rw [max_eq_right h] at h1; omega
    · rw [max_eq_left h] at h1; omega
  obtain ⟨j0, hj01, hj0i, hj0eq⟩ := exists_lpf S (show 0 < lpf S i by omega)
  have hE : sub S i (i + ℓ - 1) = (S.drop (i - 1)).take ℓ := sub_eq_window S hi1 (by omega)
  have hsrc : sub S j0 (j0 + ℓ - 1) = sub S i (i + ℓ - 1) := by
    rw [hE, sub_eq_window S hj01 (by omega)]
    rw [hlpf] at hj0eq
    exact take_eq_of_lcpAt S hj0eq
  have hex : ∃ j, 1 ≤ j ∧ sub S j (j + ℓ - 1) = sub S i (i + ℓ - 1) := ⟨j0, hj01, hsrc⟩
  obtain ⟨i', hi'def⟩ : ∃ i', i' = Nat.find hex := ⟨_, rfl⟩
  have hi'spec : 1 ≤ i' ∧ sub S i' (i' + ℓ - 1) = sub S i (i + ℓ - 1) := by
    rw [hi'def]; exact Nat.find_spec hex
  have hi'lt : i' < i := by
    have : i' ≤ j0 := by rw [hi'def]; exact Nat.find_min' hex ⟨hj01, hsrc⟩
    omega
  have hi'min : ∀ j, 1 ≤ j → j < i' → sub S j (j + ℓ - 1) ≠ sub S i (i + ℓ - 1) := by
    intro j hj1 hj heq
    rw [hi'def] at hj
    exact Nat.find_min hex hj ⟨hj1, heq⟩
  -- phrase starts in both occurrences (Claim 8.10 and Fact 8.9)
  obtain ⟨b, hb⟩ : (Finset.Ico i (i + ℓ) ∩ ((LZ77 S).map Prod.fst).toFinset).Nonempty := by
    have h := DynLZ77.Main.claim_8_10 S i hiIred
    rw [← hℓ] at h
    exact Finset.card_pos.1 (by omega)
  rw [Finset.mem_inter, Finset.mem_Ico] at hb
  obtain ⟨⟨hb1, hb2⟩, hbZ⟩ := hb
  obtain ⟨x', y', hxy', hx'1, hx'2⟩ := DynLZ77.Main.fact_8_9 S i' (i' + ℓ - 1) hi'spec.1
    (by omega) (by omega) (by
      intro i'' h1 h2 heq
      rw [show i'' + (i' + ℓ - 1 - i') = i'' + ℓ - 1 by omega, hi'spec.2] at heq
      exact hi'min i'' h1 h2 heq)
  have hb'Z : x' ∈ ((LZ77 S).map Prod.fst).toFinset :=
    List.mem_toFinset.2 (List.mem_map.2 ⟨(x', y'), hxy', rfl⟩)
  -- a window of length `3τ − 1` inside `S[i..i+ℓ)` with period `> τ/3` (Lemma 8.8)
  have hElen : (sub S i (i + ℓ - 1)).length = ℓ := length_sub_eq S hi1 (by omega) (by omega)
  unfold HighlyPeriodic at hnp
  rw [hElen] at hnp
  obtain ⟨i0, hi01, hi02, hi03⟩ := DynLZ77.Main.lemma_8_8 (sub S i (i + ℓ - 1))
    ((τ / 3 + 1 : ℕ) : ℤ) (by exact_mod_cast (show τ / 3 + 1 ≤ per (sub S i (i + ℓ - 1)) by omega))
    (3 * τ - 1) (by exact_mod_cast (show 2 * (τ / 3 + 1) ≤ 3 * τ - 1 by omega)) (by omega)
  have hW : sub (sub S i (i + ℓ - 1)) i0 (i0 + (3 * τ - 1) - 1) =
      sub S (i + i0 - 1) (i + i0 - 1 + 3 * τ - 2) := by
    rw [sub_of_sub S hi1 hi01 (by omega) (by omega),
      show i + (i0 + (3 * τ - 1) - 1) - 1 = i + i0 - 1 + 3 * τ - 2 by omega]
  rw [hW] at hi03
  rw [hElen] at hi02
  have hper : τ / 3 + 1 ≤ per (sub S (i + i0 - 1) (i + i0 - 1 + 3 * τ - 2)) := by
    exact_mod_cast hi03
  -- density gives a synchronizing position `x ∈ [m..m+τ)`, `m = i + i0 − 1`
  have hclose : ∀ y, (∃ c ∈ ((LZ77 S).map Prod.fst).toFinset, c ≤ y + 10 * τ ∧ y ≤ c + 10 * τ) →
      y ∈ close τ ((LZ77 S).map Prod.fst).toFinset := by
    rintro y ⟨c, hc, h1, h2⟩
    unfold close
    rw [Finset.mem_biUnion]
    exact ⟨c, hc, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩
  have hmD : i + i0 - 1 ∈ close τ ((LZ77 S).map Prod.fst).toFinset ∩
      Finset.Icc 1 (S.length + 2 - 3 * τ) :=
    Finset.mem_inter.2 ⟨hclose _ ⟨b, hbZ, by omega, by omega⟩,
      Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩
  have hdens := (hsync.2 _ hmD).not.2 (by
    intro h
    have := three_mul_le_of_real h
    omega)
  push Not at hdens
  obtain ⟨x, hx, hxSy⟩ := hdens
  rw [Finset.mem_Ico] at hx
  obtain ⟨k', rfl⟩ : ∃ k', x = i + k' := ⟨x - i, by omega⟩
  -- consistency puts `i′ + k′` in `Sy`
  have hwin : sub S (i + k') (i + k' + 2 * τ - 1) = sub S (i' + k') (i' + k' + 2 * τ - 1) := by
    rw [show i + k' + 2 * τ - 1 = i + (k' + 2 * τ) - 1 by omega,
      show i' + k' + 2 * τ - 1 = i' + (k' + 2 * τ) - 1 by omega,
      show i + k' = i + (k' + 1) - 1 by omega, show i' + k' = i' + (k' + 1) - 1 by omega,
      ← sub_of_sub S hi1 (by omega) (by omega) (show k' + 2 * τ ≤ i + ℓ - 1 + 1 - i by omega),
      ← sub_of_sub S hi'spec.1 (by omega) (by omega)
        (show k' + 2 * τ ≤ i' + ℓ - 1 + 1 - i' by omega), hi'spec.2]
  have hy : i' + k' ∈ Sy := by
    refine (hsync.1 (i + k') (Finset.mem_inter.2 ⟨hclose _ ⟨b, hbZ, by omega, by omega⟩,
      Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩) (i' + k')
      (Finset.mem_inter.2 ⟨hclose _ ⟨x', hb'Z, by omega, by omega⟩,
        Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩) hwin).1 hxSy
  -- Claim 8.11: `(k′+1, ℓ−k′)` is a non-dominated extension point of `i + k′`
  obtain ⟨hnot, hlcs, hlcp⟩ := DynLZ77.Main.claim_8_11 S i hiIred ℓ hℓ i' hi'spec.1 hi'lt
    hi'spec.2.symm k' (by omega)
  refine ⟨i + k', Finset.mem_filter.2 ⟨hxSy, by omega, by omega⟩, (k' + 1, ℓ - k'), ?_, by omega⟩
  unfold dext nonDominated
  have hmem : (k' + 1, ℓ - k') ∈ ext S (Sy.filter (fun a => 1 ≤ a ∧ a ≤ S.length)) (i + k') := by
    unfold ext
    rw [Finset.mem_image]
    refine ⟨i' + k', Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hy, by omega, by omega⟩, by omega⟩, ?_⟩
    unfold extPoint
    rw [hlcs, hlcp]
  rw [Finset.mem_filter]
  refine ⟨hmem, fun q' hq' hne hdom => ?_⟩
  unfold ext at hq'
  rw [Finset.mem_image] at hq'
  obtain ⟨j, hj, rfl⟩ := hq'
  rw [Finset.mem_filter, Finset.mem_filter] at hj
  unfold extPoint at hne hdom
  apply hnot
  refine ⟨j, hj.1.2.1, hj.2, hdom.1, hdom.2, ?_⟩
  by_contra hns
  push Not at hns
  exact hne (Prod.ext (by simp only; omega) (by simp only; omega))

omit [DecidableEq α] in
theorem starts_mem_Icc (S : List α) [DecidableEq α] :
    ((LZ77 S).map Prod.fst).toFinset ⊆ Finset.Icc 1 S.length := by
  intro x hx
  rw [List.mem_toFinset] at hx
  have h := starts_bounds S 1 le_rfl x hx
  exact Finset.mem_Icc.2 h

theorem card_starts_le (S : List α) : (((LZ77 S).map Prod.fst).toFinset.card : ℝ) ≤ (z S : ℝ) := by
  have h := List.toFinset_card_le ((LZ77 S).map Prod.fst)
  rw [List.length_map] at h
  exact_mod_cast h

theorem one_le_L (n : ℕ) : 1 ≤ 1 + Real.logb 2 (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [h, Nat.cast_zero, Real.logb_zero]
    norm_num
  · have : 0 ≤ Real.logb 2 (n : ℝ) :=
      Real.logb_nonneg one_lt_two (by exact_mod_cast h)
    linarith

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

open Classical in
/-- Small dyadic classes (`LPF′(i) < 32`): map `i` to the phrase start in `E_i` (Claim 8.10). -/
theorem aper_small_le (S : List α) {k : ℕ} (hk : k ≤ 4) :
    ((Ired S).filter
        (fun i => ¬ HighlyPeriodic (sub S i (i + lpf' S i - 1)) ∧ Nat.log 2 (lpf' S i) = k)).card ≤
      32 * ((LZ77 S).map Prod.fst).toFinset.card := by
  have hsub : (Ired S).filter
        (fun i => ¬ HighlyPeriodic (sub S i (i + lpf' S i - 1)) ∧ Nat.log 2 (lpf' S i) = k) ⊆
      ((LZ77 S).map Prod.fst).toFinset.biUnion (fun b => Finset.Icc (b - 31) b) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hiIred, -, hlog⟩ := hi
    obtain ⟨b, hb⟩ : (Finset.Ico i (i + lpf' S i) ∩ ((LZ77 S).map Prod.fst).toFinset).Nonempty :=
      Finset.card_pos.1 (by rw [DynLZ77.Main.claim_8_10 S i hiIred]; omega)
    rw [Finset.mem_inter, Finset.mem_Ico] at hb
    have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (lpf' S i)
    rw [hlog] at hlt
    have h32 : 2 ^ k.succ ≤ 32 := by
      calc 2 ^ k.succ ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 32 := by norm_num
    rw [Finset.mem_biUnion]
    exact ⟨b, hb.2, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ b ∈ ((LZ77 S).map Prod.fst).toFinset, (Finset.Icc (b - 31) b).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _b ∈ ((LZ77 S).map Prod.fst).toFinset, 32 :=
        Finset.sum_le_sum (fun b _ => by rw [Nat.card_Icc]; omega)
    _ = 32 * ((LZ77 S).map Prod.fst).toFinset.card := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]

open Classical in
/-- Large dyadic classes (`k ≥ 5`): at most `∑_{a ∈ Sync} |DExt_Sync(a)|`, bounded by Lemma 2.2
and Lemma 8.4. -/
theorem aper_large_le {C84 : ℝ}
    (h84 : ∀ {α : Type} [DecidableEq α] (T : List α) (I : Finset ℕ) (τ : ℕ),
      I ⊆ Finset.Icc 1 T.length → 1 ≤ τ → τ ≤ T.length / 2 →
        ∃ Sy : Finset ℕ, IsLocalSyncSet T I τ Sy ∧ (Sy.card : ℝ) ≤ C84 * (I.card : ℝ))
    {C22 : ℝ} (h22 : ∀ {α : Type} [DecidableEq α] (S : List α) (I : Finset ℕ),
      I ⊆ Finset.Icc 1 S.length →
        ((∑ i ∈ I, (dext S I i).card : ℕ) : ℝ) ≤
          C22 * (I.card : ℝ) * (1 + Real.logb 2 (S.length : ℝ)) ^ 2)
    (S : List α) {k : ℕ} (hk : 5 ≤ k) :
    (((Ired S).filter
        (fun i => ¬ HighlyPeriodic (sub S i (i + lpf' S i - 1)) ∧ Nat.log 2 (lpf' S i) = k)).card : ℝ) ≤
      max C22 0 * max C84 0 * (((LZ77 S).map Prod.fst).toFinset.card : ℝ) *
        (1 + Real.logb 2 (S.length : ℝ)) ^ 2 := by
  have hL := one_le_L S.length
  have hnn : 0 ≤ max C22 0 * max C84 0 * (((LZ77 S).map Prod.fst).toFinset.card : ℝ) *
      (1 + Real.logb 2 (S.length : ℝ)) ^ 2 := by positivity
  by_cases hne : ((Ired S).filter
      (fun i => ¬ HighlyPeriodic (sub S i (i + lpf' S i - 1)) ∧ Nat.log 2 (lpf' S i) = k)).Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.card_empty, Nat.cast_zero]
    exact hnn
  obtain ⟨i0, hi0⟩ := hne
  have hi0' := hi0
  rw [Finset.mem_filter] at hi0'
  obtain ⟨hi0Ired, -, hlog0⟩ := hi0'
  rw [Ired, Finset.mem_filter, Finset.mem_Icc] at hi0Ired
  have hX : 2 ^ k ≤ lpf' S i0 := by
    rw [← hlog0]
    exact Nat.pow_log_le_self 2 (by have := lt_add_lpf' S i0; omega)
  have hfit := add_lpf'_le S hi0Ired.1.1 hi0Ired.1.2
  have h32 : 32 ≤ 2 ^ k := by
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨Sy, hsync, hcard⟩ := h84 S ((LZ77 S).map Prod.fst).toFinset (2 ^ k / 3 - 1)
    (starts_mem_Icc S) (by omega) (by omega)
  have hsubI : Sy.filter (fun a => 1 ≤ a ∧ a ≤ S.length) ⊆ Finset.Icc 1 S.length := by
    intro a ha
    rw [Finset.mem_filter] at ha
    exact Finset.mem_Icc.2 ha.2
  have h22' := h22 S (Sy.filter (fun a => 1 ≤ a ∧ a ≤ S.length)) hsubI
  have hsub : (Ired S).filter
        (fun i => ¬ HighlyPeriodic (sub S i (i + lpf' S i - 1)) ∧ Nat.log 2 (lpf' S i) = k) ⊆
      ((Sy.filter (fun a => 1 ≤ a ∧ a ≤ S.length)).sigma
        (fun a => dext S (Sy.filter (fun a => 1 ≤ a ∧ a ≤ S.length)) a)).image
          (fun p => p.1 + 1 - p.2.1) := by
    intro i hi
    obtain ⟨x, hx, q, hq, hxq⟩ := aper_core S hk Sy hsync i hi
    rw [Finset.mem_image]
    exact ⟨⟨x, q⟩, Finset.mem_sigma.2 ⟨hx, hq⟩, hxq⟩
  have hcardA := (Finset.card_le_card hsub).trans Finset.card_image_le
  rw [Finset.card_sigma] at hcardA
  have hSy' : ((Sy.filter (fun a => 1 ≤ a ∧ a ≤ S.length)).card : ℝ) ≤ Sy.card := by
    exact_mod_cast Finset.card_filter_le _ _
  have hSyZ : (Sy.card : ℝ) ≤ max C84 0 * (((LZ77 S).map Prod.fst).toFinset.card : ℝ) :=
    hcard.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  calc (((Ired S).filter
        (fun i => ¬ HighlyPeriodic (sub S i (i + lpf' S i - 1)) ∧ Nat.log 2 (lpf' S i) = k)).card : ℝ)
      ≤ ((∑ a ∈ Sy.filter (fun a => 1 ≤ a ∧ a ≤ S.length),
          (dext S (Sy.filter (fun a => 1 ≤ a ∧ a ≤ S.length)) a).card : ℕ) : ℝ) := by
        exact_mod_cast hcardA
    _ ≤ C22 * ((Sy.filter (fun a => 1 ≤ a ∧ a ≤ S.length)).card : ℝ) *
          (1 + Real.logb 2 (S.length : ℝ)) ^ 2 := h22'
    _ ≤ max C22 0 * ((Sy.filter (fun a => 1 ≤ a ∧ a ≤ S.length)).card : ℝ) *
          (1 + Real.logb 2 (S.length : ℝ)) ^ 2 := by
        gcongr
        exact le_max_left _ _
    _ ≤ max C22 0 * (max C84 0 * (((LZ77 S).map Prod.fst).toFinset.card : ℝ)) *
          (1 + Real.logb 2 (S.length : ℝ)) ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hSy'.trans hSyZ) (le_max_right _ _)) (by positivity)
    _ = max C22 0 * max C84 0 * (((LZ77 S).map Prod.fst).toFinset.card : ℝ) *
          (1 + Real.logb 2 (S.length : ℝ)) ^ 2 := by ring

omit [DecidableEq α] in
open Classical in
/-- **Lemma 1.2** from Lemma 8.4, Lemma 2.2 and the bound on `Ired_Per`: the non-highly-periodic
part is bounded class by class (`O(z log² n)` per dyadic class, `⌊log₂ n⌋ + 1` classes). -/
theorem lemma_1_2_main {C84 : ℝ}
    (h84 : ∀ {α : Type} [DecidableEq α] (T : List α) (I : Finset ℕ) (τ : ℕ),
      I ⊆ Finset.Icc 1 T.length → 1 ≤ τ → τ ≤ T.length / 2 →
        ∃ Sy : Finset ℕ, IsLocalSyncSet T I τ Sy ∧ (Sy.card : ℝ) ≤ C84 * (I.card : ℝ))
    {C22 : ℝ} (h22 : ∀ {α : Type} [DecidableEq α] (S : List α) (I : Finset ℕ),
      I ⊆ Finset.Icc 1 S.length →
        ((∑ i ∈ I, (dext S I i).card : ℕ) : ℝ) ≤
          C22 * (I.card : ℝ) * (1 + Real.logb 2 (S.length : ℝ)) ^ 2)
    {CP : ℝ} (hP : ∀ {α : Type} [DecidableEq α] (S : List α),
      (((Ired S).filter (fun i => HighlyPeriodic (sub S i (i + lpf' S i - 1)))).card : ℝ) ≤
        CP * (z S : ℝ) * (1 + Real.logb 2 (S.length : ℝ)) ^ 3) :
    ∀ {α : Type} [DecidableEq α] (S : List α),
      ((Ired S).card : ℝ) ≤ (32 + max C22 0 * max C84 0 + max CP 0) * (z S : ℝ) *
        (1 + Real.logb 2 (S.length : ℝ)) ^ 3 := by
  intro α _ S
  have hL1 := one_le_L S.length
  have hL2 : 1 ≤ (1 + Real.logb 2 (S.length : ℝ)) ^ 2 := one_le_pow₀ hL1
  have hZ := card_starts_le S
  have hZnn : (0 : ℝ) ≤ (((LZ77 S).map Prod.fst).toFinset.card : ℝ) := Nat.cast_nonneg _
  have hznn : (0 : ℝ) ≤ (z S : ℝ) := Nat.cast_nonneg _
  have hM : 0 ≤ max C22 0 * max C84 0 := mul_nonneg (le_max_right _ _) (le_max_right _ _)
  -- the non-highly-periodic part, class by class
  have hclass : ∀ k, (((Ired S).filter (fun i => ¬ HighlyPeriodic (sub S i (i + lpf' S i - 1)) ∧
      Nat.log 2 (lpf' S i) = k)).card : ℝ) ≤ (32 + max C22 0 * max C84 0) *
        (((LZ77 S).map Prod.fst).toFinset.card : ℝ) * (1 + Real.logb 2 (S.length : ℝ)) ^ 2 := by
    intro k
    by_cases hk : k ≤ 4
    · have h : (((Ired S).filter (fun i => ¬ HighlyPeriodic (sub S i (i + lpf' S i - 1)) ∧
          Nat.log 2 (lpf' S i) = k)).card : ℝ) ≤ 32 * (((LZ77 S).map Prod.fst).toFinset.card : ℝ) := by
        exact_mod_cast aper_small_le S hk
      nlinarith [mul_nonneg hZnn (sub_nonneg.2 hL2), mul_nonneg hM hZnn,
        mul_nonneg (mul_nonneg hM hZnn) (le_trans zero_le_one hL2)]
    · have h := aper_large_le h84 h22 S (show 5 ≤ k by omega)
      nlinarith [mul_nonneg hZnn (le_trans zero_le_one hL2)]
  have haper : (Ired S).filter (fun i => ¬ HighlyPeriodic (sub S i (i + lpf' S i - 1))) ⊆
      (Finset.range (Nat.log 2 S.length + 1)).biUnion (fun k => (Ired S).filter
        (fun i => ¬ HighlyPeriodic (sub S i (i + lpf' S i - 1)) ∧ Nat.log 2 (lpf' S i) = k)) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    rw [Finset.mem_biUnion]
    refine ⟨Nat.log 2 (lpf' S i), Finset.mem_range.2 ?_, Finset.mem_filter.2 ⟨hi.1, hi.2, rfl⟩⟩
    have h := hi.1
    rw [Ired, Finset.mem_filter, Finset.mem_Icc] at h
    have hfit := add_lpf'_le S h.1.1 h.1.2
    have := Nat.log_mono_right (b := 2) (show lpf' S i ≤ S.length by omega)
    omega
  have hAper : (((Ired S).filter (fun i => ¬ HighlyPeriodic (sub S i (i + lpf' S i - 1)))).card : ℝ)
      ≤ (32 + max C22 0 * max C84 0) * (z S : ℝ) * (1 + Real.logb 2 (S.length : ℝ)) ^ 3 := by
    have h1 := (Finset.card_le_card haper).trans Finset.card_biUnion_le
    have h1' : (((Ired S).filter (fun i => ¬ HighlyPeriodic (sub S i (i + lpf' S i - 1)))).card : ℝ)
        ≤ ∑ k ∈ Finset.range (Nat.log 2 S.length + 1), (((Ired S).filter
          (fun i => ¬ HighlyPeriodic (sub S i (i + lpf' S i - 1)) ∧
            Nat.log 2 (lpf' S i) = k)).card : ℝ) := by
      exact_mod_cast h1
    have h2 := Finset.sum_le_sum (s := Finset.range (Nat.log 2 S.length + 1)) (fun k _ => hclass k)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    have h3 := natLog_le_L S.length
    have hB : 0 ≤ (32 + max C22 0 * max C84 0) * (((LZ77 S).map Prod.fst).toFinset.card : ℝ) *
        (1 + Real.logb 2 (S.length : ℝ)) ^ 2 := by positivity
    calc _ ≤ _ := h1'.trans h2
      _ ≤ (1 + Real.logb 2 (S.length : ℝ)) * ((32 + max C22 0 * max C84 0) *
          (((LZ77 S).map Prod.fst).toFinset.card : ℝ) * (1 + Real.logb 2 (S.length : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast h3) hB
      _ = (32 + max C22 0 * max C84 0) * (((LZ77 S).map Prod.fst).toFinset.card : ℝ) *
          (1 + Real.logb 2 (S.length : ℝ)) ^ 3 := by ring
      _ ≤ (32 + max C22 0 * max C84 0) * (z S : ℝ) * (1 + Real.logb 2 (S.length : ℝ)) ^ 3 := by
        gcongr
  have hPer : (((Ired S).filter (fun i => HighlyPeriodic (sub S i (i + lpf' S i - 1)))).card : ℝ)
      ≤ max CP 0 * (z S : ℝ) * (1 + Real.logb 2 (S.length : ℝ)) ^ 3 :=
    (hP S).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hznn) (by positivity))
  have hsplit := Finset.card_filter_add_card_filter_not (s := Ired S)
    (fun i => HighlyPeriodic (sub S i (i + lpf' S i - 1)))
  have hsplit' : ((Ired S).card : ℝ) =
      (((Ired S).filter (fun i => HighlyPeriodic (sub S i (i + lpf' S i - 1)))).card : ℝ) +
      (((Ired S).filter (fun i => ¬ HighlyPeriodic (sub S i (i + lpf' S i - 1)))).card : ℝ) := by
    exact_mod_cast hsplit.symm
  rw [hsplit']
  nlinarith [hAper, hPer]

end DynLZ77.Main.Aux
open DynLZ77.Main

/-- **Lemma 1.2** (p. 2; proved in §8.2). There is a universal constant `C` such that every
string `S` has `|Ired_S| ≤ C·z·(1 + log₂|S|)³`, `z = |LZ77(S)|`.

Reduced to Lemma 2.2 ([BGK25, Lemma 17]) and to the bound on `Ired_Per` (pp. 52–53); the
non-highly-periodic part `Ired_Aper` (pp. 51–52) is proved here from Lemma 8.4, Lemma 8.8,
Fact 8.9 and Claims 8.10–8.11. -/
theorem solution : ∃ C : ℝ, ∀ {α : Type} [DecidableEq α] (S : List α),
    ((Ired S).card : ℝ) ≤ C * (z S : ℝ) * (1 + Real.logb 2 (S.length : ℝ)) ^ 3 := by
  obtain ⟨C84, h84⟩ := DynLZ77.Main.lemma_8_4
  obtain ⟨C22, h22⟩ := DynLZ77.Main.lemma_2_2
  obtain ⟨CP, hP⟩ := DynLZ77.Main.lemma_1_2_per
  exact ⟨_, DynLZ77.Main.Aux.lemma_1_2_main h84 h22 hP⟩
