-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_signed_grid_residual_expected_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T14:30:24.627728+00:00
-- url     : https://prove2.me/submissions/d874ee43-14fb-4809-886d-53b92e1a0287

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- A correctly normalised constant has a finite integral unless it is
    zero, in which case integrability is immediate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (F G : Ω → ℝ) (B : ℝ)
    (hF : Integrable F P) (hG : Integrable G P)
    (hConst : (∫ ω : Ω, B ∂P) = B)
    (hPath : ∀ᵐ ω ∂P, F ω ≤ B + G ω)
    (hResidual : (∫ ω, G ω ∂P) ≤ 0) :
    (∫ ω, F ω ∂P) ≤ B := by
  have hBint : Integrable (fun _ : Ω => B) P := by
    by_cases hB : B = 0
    · simpa [hB] using (integrable_zero : Integrable (fun _ : Ω => (0 : ℝ)) P)
    · by_contra hNot
      have hZero : (∫ ω : Ω, B ∂P) = 0 := integral_undef hNot
      exact hB (hConst.symm.trans hZero)
  have hBG : Integrable (fun ω => B + G ω) P := hBint.add hG
  calc
    (∫ ω, F ω ∂P) ≤ (∫ ω, B + G ω ∂P) :=
      integral_mono_ae hF hBG hPath
    _ = B + (∫ ω, G ω ∂P) := by
      rw [integral_add hBint hG]
      rw [hConst]
    _ ≤ B := by linarith
