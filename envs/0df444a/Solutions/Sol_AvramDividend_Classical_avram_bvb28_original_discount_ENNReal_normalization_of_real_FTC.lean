-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb28_original_discount_ENNReal_normalization_of_real_FTC
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:19:21.181825+00:00
-- url     : https://prove2.me/submissions/08ef6811-4e18-4ed9-8b5d-30062078c253

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (q T : ℝ) (hq : 0 < q) (hT : 0 < T)
    (hReal : q * (∫ t in Ioc (0 : ℝ) T,
        Real.exp (-(q * t)) ∂(volume : Measure ℝ)) +
        Real.exp (-(q * T)) = 1) :
    ENNReal.ofReal q *
      (∫⁻ t in Ioc (0 : ℝ) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ)) +
      ENNReal.ofReal (Real.exp (-(q * T))) = 1  := by
  have hcont : Continuous (fun t : ℝ => Real.exp (-(q * t))) := by
    fun_prop
  have hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (Ioc (0 : ℝ) T) (volume : Measure ℝ) :=
    hcont.integrableOn_Ioc
  have hNonneg : 0 ≤ ∫ t in Ioc (0 : ℝ) T,
      Real.exp (-(q * t)) ∂(volume : Measure ℝ) := by
    exact integral_nonneg (fun t => (Real.exp_pos _).le)
  have hFactor : 0 ≤ q * (∫ t in Ioc (0 : ℝ) T,
      Real.exp (-(q * t)) ∂(volume : Measure ℝ)) :=
    mul_nonneg hq.le hNonneg
  have hEnd : 0 ≤ Real.exp (-(q * T)) := (Real.exp_pos _).le
  have hEqReal :
      ENNReal.ofReal (∫ t in Ioc (0 : ℝ) T,
        Real.exp (-(q * t)) ∂(volume : Measure ℝ)) =
      ∫⁻ t in Ioc (0 : ℝ) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ) :=
    ofReal_integral_eq_lintegral_ofReal hInt
      (Filter.Eventually.of_forall (fun t => (Real.exp_pos _).le))
  have hEq := congrArg ENNReal.ofReal hReal
  rw [ENNReal.ofReal_add hFactor hEnd,
    ENNReal.ofReal_mul hq.le,
    hEqReal] at hEq
  simpa using hEq
