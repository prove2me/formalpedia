-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_shifted_compensator_real_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T08:28:40.017015+00:00
-- url     : https://prove2.me/submissions/171b1c34-d716-4c47-8ca2-b51293364555

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.FunProp
import Theorems.Thm_AvramDividend_Classical_gaussian_shifted_compensator_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_compensated_jump_pos_linear

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- Real integrability of the nonnegative Esscher jump compensator. -/
theorem solution (μ : Measure ℝ) (φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    IntegrableOn (fun z : ℝ =>
      Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z))
      (Ioi (0 : ℝ)) μ := by
  let ν : Measure ℝ := μ.restrict (Ioi (0 : ℝ))
  have hm : Measurable (fun z : ℝ =>
      Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z)) := by
    fun_prop
  have hmeas : AEStronglyMeasurable (fun z : ℝ =>
      Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z)) ν :=
    hm.aestronglyMeasurable
  have hmem : ∀ᵐ z : ℝ ∂ν, z ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem (μ := μ) measurableSet_Ioi
  have hnonneg : ∀ᵐ z : ℝ ∂ν,
      0 ≤ Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z) := by
    filter_upwards [hmem] with z hz
    change 0 < z at hz
    exact mul_nonneg (le_of_lt (Real.exp_pos _))
      (gaussian_compensated_jump_pos_linear θ z hθ hz.le).1
  have hfin :=
    gaussian_shifted_compensator_integrable μ φ θ hφ hθ hlevy
  change (∫⁻ z : ℝ,
    ENNReal.ofReal
      (Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z)) ∂ν) < ⊤ at hfin
  change Integrable (fun z : ℝ =>
    Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z)) ν
  exact (lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg).mp
    (ne_of_lt hfin)
