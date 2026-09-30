-- Prove2me | solution 1 for ComputationalLearning.modest_boosting
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T04:13:30.845318+00:00
-- url     : https://prove2.me/submissions/ab1272c1-d1b7-45b6-b74f-bb7606f6d37d

import Mathlib
import Definitions.Def_ComputationalLearning_Boosting

open MeasureTheory ProbabilityTheory


namespace ComputationalLearning

section Modest

variable {X : Type*} [MeasurableSpace X]

/-- The real inequality behind Lemma 4.1. -/
lemma modest_alg {β w r x y z n : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2) (hrw : r + w = 1)
    (hw : w ≤ β) (hx0 : 0 ≤ x) (hxr : x ≤ r) (hy0 : 0 ≤ y) (hyw : y ≤ w)
    (hn : n = x + (w - y)) (hz0 : 0 ≤ z)
    (h2 : 1 / 2 * (r⁻¹ * x) + 1 / 2 * (w⁻¹ * y) ≤ β) (h3 : n⁻¹ * z ≤ β) (hzn : z ≤ n) :
    y + z ≤ 3 * β ^ 2 - 2 * β ^ 3 := by
  have hr : 0 < r := by linarith
  -- z ≤ β n
  have hz : z ≤ β * n := by
    rcases eq_or_lt_of_le (show 0 ≤ n by linarith) with hn0 | hnpos
    · rw [← hn0] at hzn ⊢; linarith
    · rw [inv_mul_le_iff₀ hnpos] at h3; linarith
  rcases eq_or_lt_of_le (show 0 ≤ w by linarith) with hw0 | hwpos
  · -- w = 0: y = 0, x ≤ 2 β r
    have hy : y = 0 := by linarith
    rw [← hw0, inv_zero, zero_mul, mul_zero, add_zero] at h2
    have hx2 : x ≤ 2 * β * r := by
      rw [← mul_assoc, show (1:ℝ) / 2 * r⁻¹ = (2 * r)⁻¹ by field_simp, inv_mul_le_iff₀ (by linarith)]
        at h2
      linarith
    rw [hy]
    have : n = x := by rw [hn, ← hw0, hy]; ring
    have hr1 : r ≤ 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hr1 (by positivity : (0:ℝ) ≤ 2 * β * β)]
  · -- general case: a = x / r, b = y / w
    set b := y / w with hb
    have hyb : y = b * w := by rw [hb]; field_simp
    have hb0 : 0 ≤ b := div_nonneg hy0 hwpos.le
    have hx2 : x ≤ r * (2 * β - b) := by
      have e : w⁻¹ * y = b := by rw [hb]; field_simp
      rw [e] at h2
      have : r⁻¹ * x ≤ 2 * β - b := by linarith
      rw [inv_mul_le_iff₀ hr] at this
      linarith
    have key : y + β * n ≤ 3 * β ^ 2 - 2 * β ^ 3 := by
      rw [hn, hyb]
      have hrr : r = 1 - w := by linarith
      rw [hrr] at hx2
      nlinarith [mul_le_mul_of_nonneg_left hx2 hβ0, mul_nonneg hb0 (sub_nonneg.mpr hw),
        mul_nonneg hβ0 (sub_nonneg.mpr hw), mul_nonneg (mul_nonneg hβ0 hwpos.le)
          (show (0:ℝ) ≤ 1 - 2 * β by linarith), mul_nonneg hβ0 hβ0,
        mul_nonneg (mul_nonneg hβ0 (sub_nonneg.mpr hw)) (show (0:ℝ) ≤ 1 - 2 * β by linarith)]
    linarith

theorem modest_main (D : Measure X) [IsProbabilityMeasure D]
    (c h₁ h₂ h₃ : X → Bool) (hc : Measurable c) (h₁m : Measurable h₁) (h₂m : Measurable h₂)
    (h₃m : Measurable h₃) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    (e₁ : errorOf D c h₁ ≤ β) (e₂ : errorOf (filtered2 D c h₁) c h₂ ≤ β)
    (e₃ : errorOf (filtered3 D h₁ h₂) c h₃ ≤ β) :
    errorOf D c (majority3 h₁ h₂ h₃) ≤ boostFun β := by
  set R : Set X := {x | h₁ x = c x} with hR
  set W : Set X := {x | h₁ x ≠ c x} with hW
  set E2 : Set X := {x | h₂ x ≠ c x} with hE2
  set E3 : Set X := {x | h₃ x ≠ c x} with hE3
  set N : Set X := {x | h₁ x ≠ h₂ x} with hN
  have hRm : MeasurableSet R := measurableSet_eq_fun h₁m hc
  have hWm : MeasurableSet W := (measurableSet_eq_fun h₁m hc).compl
  have hE2m : MeasurableSet E2 := (measurableSet_eq_fun h₂m hc).compl
  have hE3m : MeasurableSet E3 := (measurableSet_eq_fun h₃m hc).compl
  have hNm : MeasurableSet N := (measurableSet_eq_fun h₁m h₂m).compl
  have hWR : W = Rᶜ := rfl
  have hrw : D.real R + D.real W = 1 := by
    rw [hWR, measureReal_compl hRm, probReal_univ]; ring
  have hw : D.real W ≤ β := e₁
  -- decomposition of N
  have hNeq : N = (R ∩ E2) ∪ (W \ E2) := by
    ext x
    simp only [hN, hR, hW, hE2, Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff,
      Set.mem_sdiff]
    cases h₁ x <;> cases h₂ x <;> cases c x <;> simp
  have hdisjN : Disjoint (R ∩ E2) (W \ E2) := by
    rw [Set.disjoint_left]
    rintro x ⟨hxR, _⟩ ⟨hxW, _⟩
    exact hxW hxR
  have hn : D.real N = D.real (R ∩ E2) + (D.real W - D.real (W ∩ E2)) := by
    rw [hNeq, measureReal_union hdisjN (hWm.diff hE2m)]
    have := measureReal_inter_add_sdiff (μ := D) (s := W) hE2m
    linarith
  -- decomposition of the majority error
  have hMeq : {x | majority3 h₁ h₂ h₃ x ≠ c x} = (W ∩ E2) ∪ (N ∩ E3) := by
    ext x
    simp only [majority3, hN, hW, hE2, hE3, Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff]
    cases h₁ x <;> cases h₂ x <;> cases h₃ x <;> cases c x <;> simp
  have hdisjM : Disjoint (W ∩ E2) (N ∩ E3) := by
    rw [Set.disjoint_left]
    rintro x ⟨hxW, hxE2⟩ ⟨hxN, _⟩
    simp only [hW, hE2, hN, Set.mem_setOf_eq] at hxW hxE2 hxN
    apply hxN
    cases h1 : h₁ x <;> cases h2 : h₂ x <;> cases hc' : c x <;> simp_all
  have hmaj : errorOf D c (majority3 h₁ h₂ h₃) = D.real (W ∩ E2) + D.real (N ∩ E3) := by
    unfold errorOf
    rw [hMeq]
    exact measureReal_union hdisjM (hNm.inter hE3m)
  -- the filtered errors
  have he2 : errorOf (filtered2 D c h₁) c h₂ =
      1 / 2 * ((D.real R)⁻¹ * D.real (R ∩ E2)) + 1 / 2 * ((D.real W)⁻¹ * D.real (W ∩ E2)) := by
    unfold errorOf filtered2
    rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
      ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _))
        (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)),
      ENNReal.toReal_mul, ENNReal.toReal_mul, cond_apply hRm, cond_apply hWm,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv]
    simp [Measure.real]
    rfl
  have he3 : errorOf (filtered3 D h₁ h₂) c h₃ = (D.real N)⁻¹ * D.real (N ∩ E3) := by
    unfold errorOf filtered3
    rw [cond_apply hNm, ENNReal.toReal_mul, ENNReal.toReal_inv]
    rfl
  rw [he2] at e₂
  rw [he3] at e₃
  rw [hmaj]
  unfold boostFun
  exact modest_alg hβ0 hβ hrw hw measureReal_nonneg (measureReal_mono Set.inter_subset_left)
    measureReal_nonneg (measureReal_mono Set.inter_subset_left) hn measureReal_nonneg e₂ e₃
    (measureReal_mono Set.inter_subset_left)

end Modest

end ComputationalLearning

open ComputationalLearning

theorem solution {X : Type*} [MeasurableSpace X] (D : Measure X) [IsProbabilityMeasure D]
    (c h₁ h₂ h₃ : X → Bool) (hc : Measurable c) (h₁m : Measurable h₁) (h₂m : Measurable h₂)
    (h₃m : Measurable h₃) {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1 / 2)
    (e₁ : errorOf D c h₁ ≤ β) (e₂ : errorOf (filtered2 D c h₁) c h₂ ≤ β)
    (e₃ : errorOf (filtered3 D h₁ h₂) c h₃ ≤ β) :
    errorOf D c (majority3 h₁ h₂ h₃) ≤ boostFun β := by
  exact modest_main D c h₁ h₂ h₃ hc h₁m h₂m h₃m hβ0 hβ e₁ e₂ e₃
