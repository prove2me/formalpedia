-- Prove2me | solution 1 for AvramDividend.Classical.avram_gb68_finitecap_compact_hessian_cutoff_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:42:40.699558+00:00
-- url     : https://prove2.me/submissions/bf3fb937-ac6d-4af5-bd1f-fd1679eae49b

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Topology
noncomputable section

/-- Interior C2 regularity gives a measurable clipped Hessian. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    Measurable (fun y : ℝ =>
      if y ∈ Icc a b then iteratedDeriv 2 w y else 0) := by
  intro a b
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
      (iteratedDerivWithin 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.continuousOn_iteratedDerivWithin (by norm_num) hu
  have heq : EqOn
      (iteratedDerivWithin 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
      (iteratedDeriv 2 w)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    iteratedDerivWithin_of_isOpen hopen
  have hc' : ContinuousOn (iteratedDeriv 2 w) (Icc a b) :=
    (hc.congr heq.symm).mono hsub
  have hp : Measurable (fun y : ℝ =>
      if y ∈ Icc a b then iteratedDeriv 2 w y else 0) := by
    classical
    exact hc'.measurable_piecewise continuousOn_const isClosed_Icc.measurableSet
  exact hp
