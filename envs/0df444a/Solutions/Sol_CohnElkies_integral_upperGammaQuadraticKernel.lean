-- Prove2me | solution 1 for CohnElkies.integral_upperGammaQuadraticKernel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:29.488992+00:00
-- url     : https://prove2.me/submissions/ab53be2e-5e76-4fc9-86c4-69a8af322f79

import Mathlib
import Definitions.Def_SpherePacking

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ℓ η : ℝ} (hℓ : 0 < ℓ)
    (T : ℝ) :
    (∫ a : ℝ in Ioi 0,
      upperGammaQuadraticKernel ℓ η T a) =
        ((ℓ * upperGammaVariance ℓ η / 2 * T ^ 2 : ℝ) : ℂ) := by
  calc
    (∫ a : ℝ in Ioi 0,
      upperGammaQuadraticKernel ℓ η T a) =
        ∫ a : ℝ in Ioi 0,
          (((T ^ 2 / 2) *
            (a ^ 2 * upperGammaMeasureDensity ℓ η a) : ℝ) : ℂ) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro a ha
          unfold upperGammaQuadraticKernel
          apply congrArg Complex.ofReal
          ring
    _ = ((∫ a : ℝ in Ioi 0,
          (T ^ 2 / 2) *
            (a ^ 2 * upperGammaMeasureDensity ℓ η a) : ℝ) : ℂ) :=
          integral_ofReal (𝕜 := ℂ)
    _ = (((T ^ 2 / 2) *
          (∫ a : ℝ in Ioi 0,
            a ^ 2 * upperGammaMeasureDensity ℓ η a) : ℝ) : ℂ) := by
          rw [MeasureTheory.integral_const_mul]
    _ = ((ℓ * upperGammaVariance ℓ η / 2 * T ^ 2 : ℝ) : ℂ) := by
          congr 1
          unfold upperGammaVariance
          field_simp [hℓ.ne']
end CohnElkies
