-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB134_clipped_finitecap_gradient_Borel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:13:05.634793+00:00
-- url     : https://prove2.me/submissions/3f58b225-bfc6-4c3c-9c6c-ec2053a15316

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    Measurable (fun y : ℝ =>
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      if y ∈ Icc a b then deriv w y else 1) := by
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  have hcap : 0 < C.toReal :=
    ENNReal.toReal_pos (ne_of_gt hC) hFiniteCap
  have hfrac : (((j + 1 : ℕ) : ℝ) /
      ((j + 2 : ℕ) : ℝ)) < 1 := by
    apply (div_lt_one (by positivity)).2
    exact_mod_cast (show j + 1 < j + 2 by omega)
  have hb : b < C.toReal := by
    dsimp [b]
    nlinarith [mul_lt_mul_of_pos_left hfrac hcap]
  have hsub : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    have ha : 0 < a := by dsimp [a]; positivity
    have hy0 : 0 ≤ y := le_trans (le_of_lt ha) hy.1
    refine ⟨lt_of_lt_of_le ha hy.1, ?_⟩
    exact (ENNReal.ofReal_lt_iff_lt_toReal hy0 hFiniteCap).2
      (lt_of_le_of_lt hy.2 hb)
  have hopen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    isOpen_Ioi.inter (isOpen_Iio.preimage ENNReal.continuous_ofReal)
  have hu : UniqueDiffOn ℝ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hopen.uniqueDiffOn
  have hc : ContinuousOn
      (iteratedDerivWithin 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.continuousOn_iteratedDerivWithin (by norm_num) hu
  have heq : EqOn
      (iteratedDerivWithin 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
      (iteratedDeriv 1 w)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    iteratedDerivWithin_of_isOpen hopen
  have hc' : ContinuousOn (deriv w) (Icc a b) := by
    simpa only [iteratedDeriv_one] using (hc.congr heq.symm).mono hsub
  have hp : Measurable (fun y : ℝ =>
      if y ∈ Icc a b then deriv w y else 1) := by
    classical
    exact hc'.measurable_piecewise continuousOn_const isClosed_Icc.measurableSet
  simpa only [a, b] using hp
