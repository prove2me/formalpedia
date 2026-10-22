-- Prove2me | solution 1 for FastBestSubset.PSI.theorem_4
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T19:44:46.276085+00:00
-- url     : https://prove2.me/submissions/42df11b6-45aa-4109-892f-e0be156b2c5c

import Mathlib
import Definitions.Def_FastBestSubset_CDSS_Setting
import Definitions.Def_FastBestSubset_PSI_CDPSI

set_option autoImplicit false

open Filter Topology

namespace FBSAux
open FastBestSubset.CDSS

/-! ### Scalar analysis of `gScalar` and `T` -/

lemma gS_eq (a l0 l1 l2 u : ℝ) (h2 : 0 ≤ l2) :
    gScalar a l0 l1 l2 u = ((1 + 2 * l2) * u ^ 2 / 2 - a * u + l1 * |u|) + a ^ 2 / (2 * (1 + 2 * l2))
      + l0 * (if u ≠ 0 then 1 else 0) := by
  have hc : (1 + 2 * l2) ≠ 0 := by positivity
  unfold gScalar
  field_simp
  ring

lemma q_lb (a l1 c u : ℝ) (hc : 0 < c) :
    -(|a| - l1) ^ 2 / (2 * c) ≤ c * u ^ 2 / 2 - a * u + l1 * |u| := by
  have h1 : a * u ≤ |a| * |u| := by rw [← abs_mul]; exact le_abs_self _
  have h2 : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  have key : (c * u ^ 2 / 2 - a * u + l1 * |u|) * (2 * c) + (|a| - l1) ^ 2
      = (c * |u| - (|a| - l1)) ^ 2 + 2 * c * (|a| * |u| - a * u) := by rw [h2]; ring
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg (c * |u| - (|a| - l1)), mul_nonneg hc.le (sub_nonneg.mpr h1)]

lemma q_lb0 (a l1 c u : ℝ) (hc : 0 < c) (ha : |a| ≤ l1) :
    0 ≤ c * u ^ 2 / 2 - a * u + l1 * |u| := by
  have h1 : a * u ≤ |a| * |u| := by rw [← abs_mul]; exact le_abs_self _
  have h3 : 0 ≤ |u| := abs_nonneg u
  nlinarith [sq_nonneg u, mul_le_mul_of_nonneg_right ha h3]

lemma T_ne_zero {a l0 l1 l2 : ℝ} (h : T a l0 l1 l2 ≠ 0) :
    Real.sqrt (2 * l0 / (1 + 2 * l2)) ≤ (|a| - l1) / (1 + 2 * l2) ∧
      T a l0 l1 l2 = Real.sign a * ((|a| - l1) / (1 + 2 * l2)) ∧ Real.sign a ≠ 0 := by
  unfold T at h ⊢
  by_cases hc : Real.sqrt (2 * l0 / (1 + 2 * l2)) ≤ (|a| - l1) / (1 + 2 * l2)
  · rw [if_pos hc] at h ⊢
    refine ⟨hc, by ring, ?_⟩
    intro h0; apply h; rw [h0]; ring
  · rw [if_neg hc] at h; exact absurd rfl h

lemma T_abs_ge {a l0 l1 l2 : ℝ} (h : T a l0 l1 l2 ≠ 0) :
    Real.sqrt (2 * l0 / (1 + 2 * l2)) ≤ |T a l0 l1 l2| := by
  obtain ⟨hc, hT, hs⟩ := T_ne_zero h
  have hpos : 0 ≤ (|a| - l1) / (1 + 2 * l2) := le_trans (Real.sqrt_nonneg _) hc
  rw [hT, abs_mul, abs_of_nonneg hpos]
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [Real.sign_of_neg ha]; simpa using hc
  · subst ha; exact absurd Real.sign_zero hs
  · rw [Real.sign_of_pos ha]; simpa using hc

lemma T_eq {a l0 l1 l2 : ℝ} (h2 : 0 ≤ l2) (h : T a l0 l1 l2 ≠ 0) :
    (1 + 2 * l2) * T a l0 l1 l2 = a - l1 * Real.sign (T a l0 l1 l2) := by
  obtain ⟨hc, hT, hs⟩ := T_ne_zero h
  have hcpos : (0 : ℝ) < 1 + 2 * l2 := by linarith
  have hpos : 0 ≤ (|a| - l1) / (1 + 2 * l2) := le_trans (Real.sqrt_nonneg _) hc
  have hpos' : 0 < (|a| - l1) / (1 + 2 * l2) := by
    rcases hpos.lt_or_eq with h' | h'
    · exact h'
    · exfalso; apply h; rw [hT, ← h']; ring
  rcases lt_trichotomy a 0 with ha | ha | ha
  · rw [Real.sign_of_neg ha] at hT
    rw [hT]
    have e : (-1:ℝ) * ((|a| - l1) / (1 + 2 * l2)) < 0 := by linarith
    rw [Real.sign_of_neg e, abs_of_neg ha]
    field_simp <;> ring
  · subst ha; exact absurd Real.sign_zero hs
  · rw [Real.sign_of_pos ha] at hT
    rw [hT]
    have e : 0 < (1:ℝ) * ((|a| - l1) / (1 + 2 * l2)) := by linarith
    rw [Real.sign_of_pos e, abs_of_pos ha]
    field_simp <;> ring

/-- `T` is a global minimizer of `gScalar`. -/
lemma T_min (a l0 l1 l2 : ℝ) (h0 : 0 ≤ l0) (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) (v : ℝ) :
    gScalar a l0 l1 l2 (T a l0 l1 l2) ≤ gScalar a l0 l1 l2 v := by
  have hT : T a l0 l1 l2 = if Real.sqrt (2 * l0 / (1 + 2 * l2)) ≤ (|a| - l1) / (1 + 2 * l2) then
      Real.sign a * ((|a| - l1) / (1 + 2 * l2)) else 0 := by
    unfold T
    by_cases h : Real.sqrt (2 * l0 / (1 + 2 * l2)) ≤ (|a| - l1) / (1 + 2 * l2)
    · rw [if_pos h, if_pos h]; ring
    · rw [if_neg h, if_neg h]
  rw [hT, gS_eq _ _ _ _ _ h2, gS_eq _ _ _ _ _ h2]
  generalize hc' : 1 + 2 * l2 = c
  have hc : 0 < c := by rw [← hc']; linarith
  have hqlb := q_lb a l1 c v hc
  generalize ht : (|a| - l1) / c = t
  have hct : c * t = |a| - l1 := by rw [← ht]; field_simp
  have hqv : -(c * t ^ 2) / 2 ≤ c * v ^ 2 / 2 - a * v + l1 * |v| := by
    have e : (|a| - l1) ^ 2 / (2 * c) = c * t ^ 2 / 2 := by rw [← hct]; field_simp
    rw [neg_div, e] at hqlb
    linarith
  have hq0 : c * (0:ℝ) ^ 2 / 2 - a * 0 + l1 * |(0:ℝ)| = 0 := by simp
  have hn0 : ¬ ((0:ℝ) ≠ 0) := by simp
  by_cases hcd : Real.sqrt (2 * l0 / c) ≤ t
  · rw [if_pos hcd]
    have hs := Real.sq_sqrt (show 0 ≤ 2 * l0 / c by positivity)
    have hss := mul_self_le_mul_self (Real.sqrt_nonneg _) hcd
    have hθ : 2 * l0 / c ≤ t ^ 2 := by nlinarith
    have hl0 : 2 * l0 ≤ c * t ^ 2 := by
      rw [div_le_iff₀ hc] at hθ; linarith
    have ht0 : 0 ≤ t := le_trans (Real.sqrt_nonneg _) hcd
    have hqT : c * (Real.sign a * t) ^ 2 / 2 - a * (Real.sign a * t) + l1 * |Real.sign a * t|
        = -(c * t ^ 2) / 2 := by
      rcases lt_trichotomy a 0 with ha | ha | ha
      · rw [Real.sign_of_neg ha]
        rw [abs_of_neg ha] at hct
        have e : |(-1:ℝ) * t| = t := by rw [abs_mul]; simp [abs_of_nonneg ht0]
        rw [e]
        linear_combination t * hct
      · subst ha
        rw [Real.sign_zero]
        simp only [abs_zero, zero_sub] at hct
        have htle : t ≤ 0 := by
          by_contra hh; push Not at hh; have := mul_pos hc hh; linarith
        have : t = 0 := le_antisymm htle ht0
        subst this; simp
      · rw [Real.sign_of_pos ha]
        rw [abs_of_pos ha] at hct
        have e : |(1:ℝ) * t| = t := by simp [abs_of_nonneg ht0]
        rw [e]
        linear_combination t * hct
    have hind : (if Real.sign a * t ≠ 0 then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
    have hm := mul_le_mul_of_nonneg_left hind h0
    by_cases hv0 : v = 0
    · subst hv0
      rw [if_neg hn0]
      linarith
    · rw [if_pos hv0]; linarith
  · rw [if_neg hcd, if_neg hn0]
    by_cases hv0 : v = 0
    · subst hv0; rw [if_neg hn0]
    · rw [if_pos hv0]
      by_cases ha : |a| ≤ l1
      · have := q_lb0 a l1 c v hc ha; linarith
      · push Not at ha
        have htp : 0 < t := by
          have : 0 < c * t := by rw [hct]; linarith
          exact pos_of_mul_pos_right this hc.le
        have hlt : t ^ 2 < 2 * l0 / c := by
          by_contra hh
          push Not at hh
          apply hcd
          calc Real.sqrt (2 * l0 / c) ≤ Real.sqrt (t ^ 2) := Real.sqrt_le_sqrt hh
            _ = t := Real.sqrt_sq htp.le
        rw [lt_div_iff₀ hc] at hlt
        linarith

/-! ### One coordinate update -/

variable {n p : ℕ}

lemma sum_split (i : Fin p) (β w : Fin p → ℝ) (hw : ∀ j, j ≠ i → w j = β j) (h : Fin p → ℝ → ℝ) :
    ∑ j, h j (w j) = h i (w i) + ∑ j ∈ Finset.univ.erase i, h j (β j) := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [hw j (Finset.ne_of_mem_erase hj)]

lemma f_split (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1) (β w : Fin p → ℝ) (i : Fin p)
    (hw : ∀ j, j ≠ i → w j = β j) :
    f D w = (1/2) * ∑ r, (D.y r - ∑ j ∈ Finset.univ.erase i, D.X r j * β j) ^ 2
      - btilde D β i * w i + (1/2) * w i ^ 2
      + D.lam1 * (|w i| + ∑ j ∈ Finset.univ.erase i, |β j|)
      + D.lam2 * (w i ^ 2 + ∑ j ∈ Finset.univ.erase i, β j ^ 2) := by
  have h1 : ∀ r, ∑ j, D.X r j * w j = D.X r i * w i + ∑ j ∈ Finset.univ.erase i, D.X r j * β j :=
    fun r => sum_split i β w hw (fun j x => D.X r j * x)
  have h2 : ∑ j, |w j| = |w i| + ∑ j ∈ Finset.univ.erase i, |β j| :=
    sum_split i β w hw (fun _ x => |x|)
  have h3 : ∑ j, w j ^ 2 = w i ^ 2 + ∑ j ∈ Finset.univ.erase i, β j ^ 2 :=
    sum_split i β w hw (fun _ x => x ^ 2)
  unfold f btilde
  simp only [h1, h2, h3]
  have h4 : ∀ r, (D.y r - (D.X r i * w i + ∑ j ∈ Finset.univ.erase i, D.X r j * β j)) ^ 2
      = (D.y r - ∑ j ∈ Finset.univ.erase i, D.X r j * β j) ^ 2
        - 2 * w i * ((D.y r - ∑ j ∈ Finset.univ.erase i, D.X r j * β j) * D.X r i)
        + w i ^ 2 * D.X r i ^ 2 := by
    intro r; ring
  simp only [h4, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hX i]
  ring

lemma l0_split (β w : Fin p → ℝ) (i : Fin p) (hw : ∀ j, j ≠ i → w j = β j) :
    (l0 w : ℝ) = (if w i ≠ 0 then 1 else 0)
      + ∑ j ∈ Finset.univ.erase i, (if β j ≠ 0 then (1:ℝ) else 0) := by
  have e : ∀ v : Fin p → ℝ, (l0 v : ℝ) = ∑ j, (if v j ≠ 0 then (1:ℝ) else 0) := by
    intro v
    simp only [l0, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [e]
  exact sum_split i β w hw (fun _ x => if x ≠ 0 then (1:ℝ) else 0)

lemma F_update (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1) (hl2 : 0 ≤ D.lam2)
    (β : Fin p → ℝ) (i : Fin p) (u : ℝ) :
    F D (Function.update β i u) = F D β + gScalar (btilde D β i) D.lam0 D.lam1 D.lam2 u
      - gScalar (btilde D β i) D.lam0 D.lam1 D.lam2 (β i) := by
  have hw : ∀ j, j ≠ i → Function.update β i u j = β j := fun j hj => Function.update_of_ne hj _ _
  have e1 := f_split D hX β (Function.update β i u) i hw
  have e2 := f_split D hX β β i (fun _ _ => rfl)
  have e3 := l0_split β (Function.update β i u) i hw
  have e4 := l0_split β β i (fun _ _ => rfl)
  simp only [Function.update_self] at e1 e3
  unfold F
  rw [e1, e2, e3, e4, gS_eq _ _ _ _ _ hl2, gS_eq _ _ _ _ _ hl2]
  ring

lemma nonspacer_desc (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1) (hl0 : 0 ≤ D.lam0)
    (hl1 : 0 ≤ D.lam1) (hl2 : 0 ≤ D.lam2) (β : Fin p → ℝ) (i : Fin p) :
    F D (Function.update β i (T (btilde D β i) D.lam0 D.lam1 D.lam2)) ≤ F D β := by
  rw [F_update D hX hl2]
  have := T_min (btilde D β i) _ _ _ hl0 hl1 hl2 (β i)
  linarith

lemma spacer_coord_desc (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1) (hl0 : 0 ≤ D.lam0)
    (hl1 : 0 ≤ D.lam1) (hl2 : 0 ≤ D.lam2) (β : Fin p → ℝ) (i : Fin p) (hβ : β i ≠ 0) :
    F D (Function.update β i (T (btilde D β i) 0 D.lam1 D.lam2)) ≤ F D β := by
  rw [F_update D hX hl2]
  have hm := T_min (btilde D β i) 0 D.lam1 D.lam2 le_rfl hl1 hl2 (β i)
  have e : ∀ u, gScalar (btilde D β i) D.lam0 D.lam1 D.lam2 u
      = gScalar (btilde D β i) 0 D.lam1 D.lam2 u + D.lam0 * (if u ≠ 0 then 1 else 0) := by
    intro u; unfold gScalar; ring
  rw [e, e (β i), if_pos hβ]
  have : (if T (btilde D β i) 0 D.lam1 D.lam2 ≠ 0 then (1:ℝ) else 0) ≤ 1 := by
    split_ifs <;> norm_num
  nlinarith

/-! ### Spacer step -/

lemma spacer_fold_desc (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1) (hl0 : 0 ≤ D.lam0)
    (hl1 : 0 ≤ D.lam1) (hl2 : 0 ≤ D.lam2) (β : Fin p → ℝ) :
    ∀ (l : List (Fin p)), l.Nodup → ∀ b : Fin p → ℝ, (∀ j ∈ l, b j = β j) →
      F D (l.foldl (fun b i => if β i ≠ 0 then
        Function.update b i (T (btilde D b i) 0 D.lam1 D.lam2) else b) b) ≤ F D b := by
  intro l
  induction l with
  | nil => intro _ b _; exact le_rfl
  | cons i l ih =>
    intro hnd b hb
    rw [List.foldl_cons]
    have hnd' := List.nodup_cons.mp hnd
    refine le_trans (ih hnd'.2 _ ?_) ?_
    · intro j hj
      have hji : j ≠ i := fun h => hnd'.1 (h ▸ hj)
      have hbj := hb j (List.mem_cons_of_mem _ hj)
      split_ifs
      · rw [Function.update_of_ne hji]; exact hbj
      · exact hbj
    · split_ifs with h
      · apply spacer_coord_desc D hX hl0 hl1 hl2
        rw [hb i (by simp)]; exact h
      · exact le_rfl

lemma spacer_desc (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1) (hl0 : 0 ≤ D.lam0)
    (hl1 : 0 ≤ D.lam1) (hl2 : 0 ≤ D.lam2) (β : Fin p → ℝ) : F D (spacer D β) ≤ F D β := by
  unfold spacer
  exact spacer_fold_desc D hX hl0 hl1 hl2 β (List.finRange p) (List.nodup_finRange p) β
    (fun _ _ => rfl)

lemma spacer_zero (D : Data n p) (β : Fin p → ℝ) (i : Fin p) (hi : β i = 0) :
    spacer D β i = 0 := by
  unfold spacer
  suffices h : ∀ (l : List (Fin p)) (b : Fin p → ℝ), (l.foldl (fun b j => if β j ≠ 0 then
      Function.update b j (T (btilde D b j) 0 D.lam1 D.lam2) else b) b) i = b i by
    rw [h]; exact hi
  intro l
  induction l with
  | nil => intro b; rfl
  | cons j l ih =>
    intro b
    rw [List.foldl_cons, ih]
    split_ifs with h
    · rw [Function.update_of_ne]; intro hij; subst hij; exact h hi
    · rfl

/-! ### Steps of Algorithm 1 -/

lemma step_pend [NeZero p] (D : Data n p) (C : ℕ) (s : State p) (h : s.pending = true) :
    (step D C s).beta = spacer D s.beta ∧ (step D C s).ptr = s.ptr ∧
      (step D C s).pending = false := by
  simp [step, h]

lemma step_nopend [NeZero p] (D : Data n p) (C : ℕ) (s : State p) (h : s.pending = false) :
    (step D C s).beta = Function.update s.beta (coord s)
      (T (btilde D s.beta (coord s)) D.lam0 D.lam1 D.lam2) ∧ (step D C s).ptr = s.ptr + 1 := by
  simp [step, h]

lemma stateAt_succ [NeZero p] (D : Data n p) (C : ℕ) (β0 : Fin p → ℝ) (k : ℕ) :
    stateAt D C β0 (k + 1) = step D C (stateAt D C β0 k) := by
  unfold stateAt; rw [Function.iterate_succ_apply']

lemma iter_succ_pend [NeZero p] (D : Data n p) (C : ℕ) (β0 : Fin p → ℝ) (k : ℕ)
    (h : (stateAt D C β0 k).pending = true) : iter D C β0 (k + 1) = spacer D (iter D C β0 k) := by
  unfold iter; rw [stateAt_succ]; exact (step_pend D C _ h).1

lemma iter_succ_nopend [NeZero p] (D : Data n p) (C : ℕ) (β0 : Fin p → ℝ) (k : ℕ)
    (h : (stateAt D C β0 k).pending = false) :
    iter D C β0 (k + 1) = Function.update (iter D C β0 k) (coord (stateAt D C β0 k))
      (T (btilde D (iter D C β0 k) (coord (stateAt D C β0 k))) D.lam0 D.lam1 D.lam2) := by
  unfold iter; rw [stateAt_succ]; exact (step_nopend D C _ h).1

lemma iter_desc [NeZero p] (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1) (hl0 : 0 ≤ D.lam0)
    (hl1 : 0 ≤ D.lam1) (hl2 : 0 ≤ D.lam2) (C : ℕ) (β0 : Fin p → ℝ) :
    ∀ k, F D (iter D C β0 k) ≤ F D β0 := by
  intro k
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    refine le_trans ?_ ih
    cases h : (stateAt D C β0 k).pending
    · rw [iter_succ_nopend D C β0 k h]; exact nonspacer_desc D hX hl0 hl1 hl2 _ _
    · rw [iter_succ_pend D C β0 k h]; exact spacer_desc D hX hl0 hl1 hl2 _

lemma ptr_succ [NeZero p] (D : Data n p) (C : ℕ) (β0 : Fin p → ℝ) (k : ℕ) :
    (stateAt D C β0 (k + 1)).ptr = (stateAt D C β0 k).ptr
      + (if (stateAt D C β0 k).pending = true then 0 else 1) := by
  rw [stateAt_succ]
  cases h : (stateAt D C β0 k).pending
  · rw [(step_nopend D C _ h).2]; simp
  · rw [(step_pend D C _ h).2.1]; simp

lemma ptr_two [NeZero p] (D : Data n p) (C : ℕ) (β0 : Fin p → ℝ) (k : ℕ) :
    (stateAt D C β0 k).ptr + 1 ≤ (stateAt D C β0 (k + 1 + 1)).ptr := by
  have h1 := ptr_succ D C β0 k
  have h2 := ptr_succ D C β0 (k + 1)
  cases h : (stateAt D C β0 k).pending
  · simp only [h] at h1
    split_ifs at h2 <;> simp at h1 <;> omega
  · have h' : (stateAt D C β0 (k + 1)).pending = false := by
      rw [stateAt_succ]; exact (step_pend D C _ h).2.2
    simp only [h] at h1
    simp only [h'] at h2
    simp at h1 h2
    omega

lemma ptr_mono_add [NeZero p] (D : Data n p) (C : ℕ) (β0 : Fin p → ℝ) (N : ℕ) :
    ∀ j, (stateAt D C β0 N).ptr + j ≤ (stateAt D C β0 (N + 2 * j)).ptr := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have := ptr_two D C β0 (N + 2 * j)
    rw [show N + 2 * (j + 1) = N + 2 * j + 1 + 1 by ring]
    omega

lemma hit [NeZero p] (D : Data n p) (C : ℕ) (β0 : Fin p → ℝ) (i : Fin p) (N : ℕ) :
    ∃ k ≥ N, (stateAt D C β0 k).pending = false ∧ coord (stateAt D C β0 k) = i := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, m = (stateAt D C β0 N).ptr * p + i.val := ⟨_, rfl⟩
  have hp := Nat.pos_of_neZero p
  have hm1 : (stateAt D C β0 N).ptr ≤ m := by
    rw [hm]; nlinarith
  have hex : ∃ j, m < (stateAt D C β0 (N + j)).ptr :=
    ⟨2 * (m + 1), by have := ptr_mono_add D C β0 N (m + 1); omega⟩
  obtain ⟨j0, hj0, hmin⟩ : ∃ j0, m < (stateAt D C β0 (N + j0)).ptr ∧
      ∀ j < j0, ¬ m < (stateAt D C β0 (N + j)).ptr :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have hj0pos : j0 ≠ 0 := by
    intro h0; rw [h0, Nat.add_zero] at hj0; omega
  obtain ⟨j1, hj1⟩ : ∃ j1, j0 = j1 + 1 := Nat.exists_eq_succ_of_ne_zero hj0pos
  have hmin1 := hmin j1 (by omega)
  rw [hj1, ← add_assoc] at hj0
  have hs := ptr_succ D C β0 (N + j1)
  have hpf : (stateAt D C β0 (N + j1)).pending = false := by
    cases hpp : (stateAt D C β0 (N + j1)).pending
    · rfl
    · rw [hpp] at hs; simp at hs; omega
  have heq : (stateAt D C β0 (N + j1)).ptr = m := by
    rw [hpf] at hs; simp at hs; omega
  refine ⟨N + j1, by omega, hpf, ?_⟩
  apply Fin.ext
  simp only [coord]
  rw [heq, hm, Nat.add_comm, Nat.add_mul_mod_self_right]
  exact Nat.mod_eq_of_lt i.isLt

/-! ### Continuity -/

lemma f_cont (D : Data n p) : Continuous (f D) := by
  unfold f; fun_prop

lemma btilde_cont (D : Data n p) (i : Fin p) : Continuous (fun β => btilde D β i) := by
  unfold btilde; fun_prop

/-! ### Limits of Algorithm 1 -/

lemma limit_props [NeZero p] (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1) (hl0 : 0 < D.lam0)
    (hl1 : 0 ≤ D.lam1) (hl2 : 0 ≤ D.lam2) (C : ℕ) (b0 bs : Fin p → ℝ)
    (hconv : Tendsto (iter D C b0) atTop (𝓝 bs)) :
    F D bs ≤ F D b0 ∧ ∀ i, bs i ≠ 0 →
      (1 + 2 * D.lam2) * bs i = btilde D bs i - D.lam1 * Real.sign (bs i) := by
  have hcoord : ∀ i, Tendsto (fun k => iter D C b0 k i) atTop (𝓝 (bs i)) :=
    fun i => ((continuous_apply i).tendsto bs).comp hconv
  have hnz : ∀ᶠ k in atTop, ∀ i, bs i ≠ 0 → iter D C b0 k i ≠ 0 := by
    rw [eventually_all]; intro i
    by_cases hi : bs i = 0
    · exact Eventually.of_forall (fun _ h => absurd hi h)
    · exact ((hcoord i).eventually_ne hi).mono (fun _ h _ => h)
  refine ⟨?_, ?_⟩
  · have hf : Tendsto (fun k => f D (iter D C b0 k)) atTop (𝓝 (f D bs)) :=
      ((f_cont D).tendsto bs).comp hconv
    have hle : ∀ᶠ k in atTop, f D (iter D C b0 k) + D.lam0 * (l0 bs : ℝ) ≤ F D b0 := by
      filter_upwards [hnz] with k hk
      have h1 := iter_desc D hX hl0.le hl1 hl2 C b0 k
      have h2 : (l0 bs : ℝ) ≤ l0 (iter D C b0 k) := by
        unfold l0
        exact_mod_cast Finset.card_le_card (fun i hi => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hk i hi)
      unfold F at h1 ⊢
      have := mul_le_mul_of_nonneg_left h2 hl0.le
      linarith
    have := le_of_tendsto (hf.add_const (D.lam0 * (l0 bs : ℝ))) hle
    unfold F at this ⊢; linarith
  · intro i hi
    have hcpos : 0 < 1 + 2 * D.lam2 := by linarith
    obtain ⟨θ, hθdef⟩ : ∃ θ, θ = Real.sqrt (2 * D.lam0 / (1 + 2 * D.lam2)) := ⟨_, rfl⟩
    have hθ : 0 < θ := by rw [hθdef]; exact Real.sqrt_pos.mpr (by positivity)
    have hsmall : ∀ᶠ k in atTop, ∀ j, bs j = 0 → |iter D C b0 k j| < θ := by
      rw [eventually_all]; intro j
      by_cases hj : bs j = 0
      · have h1 := (hcoord j).eventually (gt_mem_nhds (show bs j < θ by rw [hj]; exact hθ))
        have h2 := (hcoord j).eventually (lt_mem_nhds (show -θ < bs j by rw [hj]; linarith))
        filter_upwards [h1, h2] with k hk1 hk2 _
        exact abs_lt.mpr ⟨hk2, hk1⟩
      · exact Eventually.of_forall (fun _ h => absurd h hj)
    obtain ⟨K, hK⟩ := eventually_atTop.mp hsmall
    have hkill : ∀ k ≥ K, ∀ j, bs j = 0 → (stateAt D C b0 k).pending = false →
        coord (stateAt D C b0 k) = j → iter D C b0 (k + 1) j = 0 := by
      intro k hk j hj hpf hcj
      have hsm := hK (k + 1) (by omega) j hj
      rw [iter_succ_nopend D C b0 k hpf] at hsm ⊢
      rw [hcj, Function.update_self] at hsm ⊢
      by_contra hne
      have := T_abs_ge hne
      rw [← hθdef] at this; linarith
    have hzero : ∀ j, bs j = 0 → ∀ᶠ k in atTop, iter D C b0 k j = 0 := by
      intro j hj
      obtain ⟨k0, hk0, hpf, hcj⟩ := hit D C b0 j K
      rw [eventually_atTop]
      refine ⟨k0 + 1, fun k hk => ?_⟩
      induction k, hk using Nat.le_induction with
      | base => exact hkill k0 hk0 j hj hpf hcj
      | succ k hk ih =>
        cases hp : (stateAt D C b0 k).pending
        · by_cases hcj' : coord (stateAt D C b0 k) = j
          · exact hkill k (by omega) j hj hp hcj'
          · rw [iter_succ_nopend D C b0 k hp, Function.update_of_ne (Ne.symm hcj')]; exact ih
        · rw [iter_succ_pend D C b0 k hp]; exact spacer_zero D _ j ih
    have hsupp : ∀ᶠ k in atTop, iter D C b0 (k + 1) i ≠ 0 :=
      ((tendsto_add_atTop_nat 1).eventually hnz).mono (fun k hk => hk i hi)
    have hcoord1 : Tendsto (fun k => iter D C b0 (k + 1) i) atTop (𝓝 (bs i)) :=
      (hcoord i).comp (tendsto_add_atTop_nat 1)
    have hsign : ∀ᶠ k in atTop, Real.sign (iter D C b0 (k + 1) i) = Real.sign (bs i) := by
      rcases lt_or_gt_of_ne hi with hneg | hpos
      · filter_upwards [hcoord1.eventually (gt_mem_nhds hneg)] with k hk
        rw [Real.sign_of_neg hk, Real.sign_of_neg hneg]
      · filter_upwards [hcoord1.eventually (lt_mem_nhds hpos)] with k hk
        rw [Real.sign_of_pos hk, Real.sign_of_pos hpos]
    have hfreq : ∃ᶠ k in atTop, (stateAt D C b0 k).pending = false ∧
        coord (stateAt D C b0 k) = i :=
      Filter.frequently_atTop.mpr (fun N => hit D C b0 i N)
    have hφ : Tendsto (fun k => (1 + 2 * D.lam2) * iter D C b0 (k + 1) i
        - btilde D (iter D C b0 k) i + D.lam1 * Real.sign (bs i)) atTop
        (𝓝 ((1 + 2 * D.lam2) * bs i - btilde D bs i + D.lam1 * Real.sign (bs i))) := by
      have hb := ((btilde_cont D i).tendsto bs).comp hconv
      exact ((hcoord1.const_mul _).sub hb).add_const _
    have hzeroφ : ∃ᶠ k in atTop, (1 + 2 * D.lam2) * iter D C b0 (k + 1) i
        - btilde D (iter D C b0 k) i + D.lam1 * Real.sign (bs i) = 0 := by
      refine (hfreq.and_eventually (hsupp.and hsign)).mono ?_
      rintro k ⟨⟨hpf, hcj⟩, hnz1, hsg⟩
      have e := iter_succ_nopend D C b0 k hpf
      rw [hcj] at e
      have ev : iter D C b0 (k + 1) i = T (btilde D (iter D C b0 k) i) D.lam0 D.lam1 D.lam2 := by
        rw [e, Function.update_self]
      rw [ev] at hnz1 hsg ⊢
      have := T_eq hl2 hnz1
      rw [hsg] at this
      linarith
    by_contra hne
    have hne' : (1 + 2 * D.lam2) * bs i - btilde D bs i + D.lam1 * Real.sign (bs i) ≠ 0 := by
      intro h; apply hne; linarith
    have hev := hφ.eventually_ne hne'
    obtain ⟨k, hk1, hk2⟩ := (hzeroφ.and_eventually hev).exists
    exact hk2 hk1

/-! ### Coordinatewise optimality on the support gives optimality on the support subspace -/

noncomputable def resid (D : Data n p) (b : Fin p → ℝ) (r : Fin n) : ℝ :=
  D.y r - ∑ j, D.X r j * b j

noncomputable def grad (D : Data n p) (b : Fin p → ℝ) (j : Fin p) : ℝ :=
  ∑ r, resid D b r * D.X r j

lemma btilde_eq (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1) (b : Fin p → ℝ) (i : Fin p) :
    btilde D b i = grad D b i + b i := by
  unfold btilde grad resid
  have h : ∀ r, D.y r - ∑ j ∈ Finset.univ.erase i, D.X r j * b j
      = (D.y r - ∑ j, D.X r j * b j) + D.X r i * b i := by
    intro r; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]; ring
  simp only [h, add_mul, Finset.sum_add_distrib]
  have h2 : ∑ r, D.X r i * b i * D.X r i = b i * ∑ r, D.X r i ^ 2 := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro _ _; ring
  rw [h2, hX i, mul_one]

lemma f_min_on_supp (D : Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1) (hl1 : 0 ≤ D.lam1)
    (hl2 : 0 ≤ D.lam2) (b : Fin p → ℝ)
    (hb : ∀ i, b i ≠ 0 → (1 + 2 * D.lam2) * b i = btilde D b i - D.lam1 * Real.sign (b i))
    (x : Fin p → ℝ) (hx : ∀ j, b j = 0 → x j = 0) : f D b ≤ f D x := by
  have hg : ∀ j, (x j - b j) * (-(grad D b j) + D.lam1 * Real.sign (b j) + 2 * D.lam2 * b j)
      = 0 := by
    intro j
    by_cases hj : b j = 0
    · rw [hj, hx j hj]; ring
    · have h1 := hb j hj
      rw [btilde_eq D hX] at h1
      have : -(grad D b j) + D.lam1 * Real.sign (b j) + 2 * D.lam2 * b j = 0 := by linarith
      rw [this, mul_zero]
  have hZ : ∑ j, (x j - b j) * (-(grad D b j) + D.lam1 * Real.sign (b j) + 2 * D.lam2 * b j)
      = -(∑ j, (x j - b j) * grad D b j) + D.lam1 * ∑ j, Real.sign (b j) * (x j - b j)
        + D.lam2 * ∑ j, 2 * b j * (x j - b j) := by
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j _; ring
  rw [Finset.sum_eq_zero (fun j _ => hg j)] at hZ
  have hres : ∀ r, D.y r - ∑ j, D.X r j * x j = resid D b r - ∑ j, D.X r j * (x j - b j) := by
    intro r; unfold resid; simp only [mul_sub, Finset.sum_sub_distrib]; ring
  have hA : ∑ r, resid D b r ^ 2 - 2 * ∑ j, (x j - b j) * grad D b j
      ≤ ∑ r, (D.y r - ∑ j, D.X r j * x j) ^ 2 := by
    have hswap : ∑ j, (x j - b j) * grad D b j
        = ∑ r, resid D b r * ∑ j, D.X r j * (x j - b j) := by
      unfold grad
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro r _; apply Finset.sum_congr rfl; intro j _; ring
    rw [hswap, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum; intro r _
    rw [hres r]
    nlinarith [sq_nonneg (∑ j, D.X r j * (x j - b j))]
  have hB : ∑ j, |b j| + ∑ j, Real.sign (b j) * (x j - b j) ≤ ∑ j, |x j| := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_le_sum; intro j _
    rcases lt_trichotomy (b j) 0 with h | h | h
    · rw [Real.sign_of_neg h, abs_of_neg h]; have := neg_abs_le (x j); linarith
    · rw [h, Real.sign_zero]; simp
    · rw [Real.sign_of_pos h, abs_of_pos h]; have := le_abs_self (x j); linarith
  have hC : ∑ j, b j ^ 2 + ∑ j, 2 * b j * (x j - b j) ≤ ∑ j, x j ^ 2 := by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_le_sum; intro j _
    nlinarith [sq_nonneg (x j - b j)]
  have hB' := mul_le_mul_of_nonneg_left hB hl1
  have hC' := mul_le_mul_of_nonneg_left hC hl2
  have hfb : ∑ r, (D.y r - ∑ j, D.X r j * b j) ^ 2 = ∑ r, resid D b r ^ 2 := rfl
  unfold f
  rw [hfb]
  linarith

/-! ### Stationarity -/

lemma stationary_of (D : Data n p) (hl0 : 0 < D.lam0) (b : Fin p → ℝ)
    (hmin : ∀ x : Fin p → ℝ, (∀ j, b j = 0 → x j = 0) → f D b ≤ f D x) : IsStationary D b := by
  intro d
  have happ : ∀ α : ℝ, ∀ i, (b + α • d) i = b i + α * d i := by intro α i; simp
  have hcont : ∀ i, Tendsto (fun α : ℝ => b i + α * d i) (𝓝[>] (0:ℝ)) (𝓝 (b i)) := by
    intro i
    have : Tendsto (fun α : ℝ => b i + α * d i) (𝓝 (0:ℝ)) (𝓝 (b i + 0 * d i)) :=
      ((continuous_const.add (continuous_id.mul continuous_const)).tendsto 0)
    rw [zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hnz : ∀ᶠ α in 𝓝[>] (0:ℝ), ∀ i, b i ≠ 0 → b i + α * d i ≠ 0 := by
    rw [eventually_all]; intro i
    by_cases hi : b i = 0
    · exact Eventually.of_forall (fun _ h => absurd hi h)
    · exact ((hcont i).eventually_ne hi).mono (fun _ h _ => h)
  have hfc : Tendsto (fun α : ℝ => f D (b + α • d)) (𝓝[>] (0:ℝ)) (𝓝 (f D b)) := by
    have : Tendsto (fun α : ℝ => b + α • d) (𝓝 (0:ℝ)) (𝓝 (b + (0:ℝ) • d)) :=
      ((continuous_const.add (continuous_id.smul continuous_const)).tendsto 0)
    rw [zero_smul, add_zero] at this
    exact ((f_cont D).tendsto b).comp (this.mono_left nhdsWithin_le_nhds)
  have hev : ∀ᶠ α in 𝓝[>] (0:ℝ), F D b ≤ F D (b + α • d) := by
    by_cases hd : ∃ j, b j = 0 ∧ d j ≠ 0
    · obtain ⟨j, hbj, hdj⟩ := hd
      have hf' := hfc.eventually (lt_mem_nhds (show f D b - D.lam0 < f D b by linarith))
      filter_upwards [hnz, hf', self_mem_nhdsWithin] with α hα hfα hαpos
      have hαpos' : 0 < α := hαpos
      have hcard : l0 b + 1 ≤ l0 (b + α • d) := by
        unfold l0
        have hsub : insert j (Finset.univ.filter (fun i => b i ≠ 0))
            ⊆ Finset.univ.filter (fun i => (b + α • d) i ≠ 0) := by
          intro i hi
          rw [Finset.mem_insert] at hi
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, happ] at hi ⊢
          rcases hi with rfl | hi
          · rw [hbj, zero_add]; exact mul_ne_zero (ne_of_gt hαpos') hdj
          · exact hα i hi
        have hnot : j ∉ Finset.univ.filter (fun i => b i ≠ 0) := by simp [hbj]
        have := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hnot] at this
        exact this
      unfold F
      have h1 : ((l0 b : ℕ) : ℝ) + 1 ≤ (l0 (b + α • d) : ℝ) := by exact_mod_cast hcard
      have := mul_le_mul_of_nonneg_left h1 hl0.le
      linarith
    · push Not at hd
      filter_upwards [hnz] with α hα
      have hmn := hmin (b + α • d) (by intro j hj; rw [happ, hj, hd j hj]; ring)
      have hcard : l0 b ≤ l0 (b + α • d) := by
        unfold l0
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, happ] at hi ⊢
        exact hα i hi
      unfold F
      have h1 : (l0 b : ℝ) ≤ (l0 (b + α • d) : ℝ) := by exact_mod_cast hcard
      have := mul_le_mul_of_nonneg_left h1 hl0.le
      linarith
  refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [hev, self_mem_nhdsWithin] with α hα hpos
  have hpos' : 0 < α := hpos
  have : 0 ≤ (F D (b + α • d) - F D b) / α := div_nonneg (by linarith) (le_of_lt hpos')
  exact_mod_cast this

end FBSAux

open FastBestSubset.PSI in
theorem solution {n p : ℕ} [NeZero p] (D : FastBestSubset.CDSS.Data n p) (hX : ∀ j, ∑ r, D.X r j ^ 2 = 1)
    (hlam0 : 0 < D.lam0) (hlam1 : 0 ≤ D.lam1) (hlam2 : 0 ≤ D.lam2)
    (hscope : D.lam1 = 0 ∨ D.lam2 = 0)
    (C : ℕ) (hC : 0 < C) (β0 : Fin p → ℝ)
    (hA : D.lam2 = 0 → (FastBestSubset.CDSS.Assumption1 D ∧ (n < p → FastBestSubset.CDSS.Assumption2 D β0)))
    (k : ℕ) (hk : 0 < k) (βhat β : ℕ → Fin p → ℝ) (hrun : IsCDPSIRun D k C β0 βhat β) :
    ∃ L : ℕ, (∀ m < L, Improving14 D k (β (m + 1))) ∧ ¬ Improving14 D k (β (L + 1)) ∧
      IsPSI D k (β (L + 1)) := by
  classical
  obtain ⟨_, hrun'⟩ := hrun
  have hlim : ∀ ℓ, (∀ m < ℓ, Improving14 D k (β (m + 1))) →
      FastBestSubset.CDSS.F D (β (ℓ + 1)) ≤ FastBestSubset.CDSS.F D (βhat ℓ) ∧
      (∀ x : Fin p → ℝ, (∀ j, β (ℓ + 1) j = 0 → x j = 0) →
        FastBestSubset.CDSS.f D (β (ℓ + 1)) ≤ FastBestSubset.CDSS.f D x) := by
    intro ℓ hℓ
    obtain ⟨h1, h2⟩ := FBSAux.limit_props D hX hlam0 hlam1 hlam2 C _ _ (hrun' ℓ hℓ).1
    exact ⟨h1, FBSAux.f_min_on_supp D hX hlam1 hlam2 _ h2⟩
  have hex : ∃ L, ¬ Improving14 D k (β (L + 1)) := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ ℓ, ∀ m < ℓ, Improving14 D k (β (m + 1)) := fun ℓ m _ => hcon m
    have hdec : ∀ ℓ, FastBestSubset.CDSS.F D (β (ℓ + 1 + 1)) < FastBestSubset.CDSS.F D (β (ℓ + 1)) := by
      intro ℓ
      have h1 := (hlim (ℓ + 1) (hall _)).1
      have h2 := ((hrun' ℓ (hall ℓ)).2 (hcon ℓ)).2
      exact lt_of_le_of_lt h1 h2
    have hanti : StrictAnti (fun ℓ => FastBestSubset.CDSS.F D (β (ℓ + 1))) :=
      strictAnti_nat_of_succ_lt hdec
    have key : ∀ a b, FastBestSubset.CDSS.supp (β (a + 1)) = FastBestSubset.CDSS.supp (β (b + 1)) →
        FastBestSubset.CDSS.F D (β (a + 1)) ≤ FastBestSubset.CDSS.F D (β (b + 1)) := by
      intro a b hab
      have hmin := (hlim a (hall a)).2 (β (b + 1)) (by
        intro j hj
        by_contra hne
        have hjm : j ∈ FastBestSubset.CDSS.supp (β (b + 1)) := by
          simp [FastBestSubset.CDSS.supp, hne]
        rw [← hab] at hjm
        simp [FastBestSubset.CDSS.supp] at hjm
        exact hjm hj)
      have hl : FastBestSubset.CDSS.l0 (β (a + 1)) = FastBestSubset.CDSS.l0 (β (b + 1)) :=
        congrArg Finset.card hab
      unfold FastBestSubset.CDSS.F; rw [hl]; linarith
    have hinj : Function.Injective (fun ℓ => FastBestSubset.CDSS.supp (β (ℓ + 1))) := by
      intro a b hab
      simp only at hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have h1 := hanti h; have h2 := key a b hab; simp only at h1; linarith
      · have h1 := hanti h; have h2 := key b a hab.symm; simp only at h1; linarith
    exact not_injective_infinite_finite _ hinj
  obtain ⟨L, hL, hLmin⟩ : ∃ L, ¬ Improving14 D k (β (L + 1)) ∧
      ∀ m < L, Improving14 D k (β (m + 1)) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => not_not.mp (Nat.find_min hex hm)⟩
  refine ⟨L, hLmin, hL, ?_, ?_⟩
  · exact FBSAux.stationary_of D hlam0 _ (hlim L hLmin).2
  · intro S1 S2 h1 h2 h3 h4 γ
    by_contra hlt
    push Not at hlt
    exact hL ⟨_, ⟨S1, S2, γ, h1, h2, h3, h4, rfl⟩, hlt⟩
