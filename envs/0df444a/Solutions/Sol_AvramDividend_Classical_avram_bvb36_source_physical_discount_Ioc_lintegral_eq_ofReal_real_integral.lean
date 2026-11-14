-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb36_source_physical_discount_Ioc_lintegral_eq_ofReal_real_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:40:31.968661+00:00
-- url     : https://prove2.me/submissions/1bbd7eec-1c8e-4d5d-8ee9-9d83a2e53991

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (q T : ℝ) :
    (∫⁻ t in Ioc (0 : ℝ) T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(volume : Measure ℝ)) =
    ENNReal.ofReal (∫ t in Ioc (0 : ℝ) T,
      Real.exp (-(q * t)) ∂(volume : Measure ℝ))  := by
  have hCont : Continuous (fun t : ℝ => Real.exp (-(q * t))) := by
    fun_prop
  have hInt : IntegrableOn (fun t : ℝ => Real.exp (-(q * t)))
      (Ioc (0 : ℝ) T) (volume : Measure ℝ) :=
    hCont.integrableOn_Ioc
  have hNonneg : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioc (0 : ℝ) T)]
      (fun t : ℝ => Real.exp (-(q * t))) :=
    Filter.Eventually.of_forall (fun t => (Real.exp_pos _).le)
  exact (ofReal_integral_eq_lintegral_ofReal hInt hNonneg).symm
