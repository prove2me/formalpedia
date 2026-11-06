-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_signed_grid_residual_expected_bound_with_integrable_constant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:25:29.894365+00:00
-- url     : https://prove2.me/submissions/de902e93-1327-4078-86f0-de820a5ea3b0

import Mathlib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Exact expected real finite-grid payoff comparison with an explicitly
    integrable initial constant and genuine nonpositive residual mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F G : Ω → ℝ) (B : ℝ)
    (hF : Integrable F P) (hG : Integrable G P)
    (hBint : Integrable (fun _ : Ω => B) P)
    (hConst : (∫ ω : Ω, B ∂P) = B)
    (hPath : ∀ᵐ ω ∂P, F ω ≤ B + G ω)
    (hResidual : (∫ ω, G ω ∂P) ≤ 0) :
    (∫ ω, F ω ∂P) ≤ B := by
  have hBG : Integrable (fun ω => B + G ω) P := hBint.add hG
  calc
    (∫ ω, F ω ∂P) ≤ (∫ ω, B + G ω ∂P) :=
      integral_mono_ae hF hBG hPath
    _ = B + (∫ ω, G ω ∂P) := by
      rw [integral_add hBint hG]
      rw [hConst]
    _ ≤ B := by linarith
