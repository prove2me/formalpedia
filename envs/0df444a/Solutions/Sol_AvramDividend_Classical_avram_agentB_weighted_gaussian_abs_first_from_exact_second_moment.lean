-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_weighted_gaussian_abs_first_from_exact_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:09:57.012756+00:00
-- url     : https://prove2.me/submissions/8451eb8e-d3db-4b76-b7a6-6fc5462a9673

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false
/-- Exact conditional second-moment factorisation bounds every
nonnegative original dividend-weighted Gaussian first absolute moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (W Z : Ω → ℝ) (v δ : ℝ) (hδ : 0 < δ)
    (hWnonneg : ∀ ω, 0 ≤ W ω)
    (hWI : Integrable W P)
    (hWZI : Integrable (fun ω => W ω * |Z ω|) P)
    (hWZ2I : Integrable (fun ω => W ω * (Z ω)^2) P)
    (hWeightedSquare : (∫ ω, W ω * (Z ω)^2 ∂P) =
      v * (∫ ω, W ω ∂P)) :
    (2 * δ) * (∫ ω, W ω * |Z ω| ∂P) ≤
      (v + δ^2) * (∫ ω, W ω ∂P) := by
  have hpoint (ω : Ω) :
      (2 * δ) * (W ω * |Z ω|) ≤
        W ω * (Z ω)^2 + δ^2 * W ω := by
    have hb : 2 * δ * |Z ω| ≤ (Z ω)^2 + δ^2 := by
      nlinarith [sq_nonneg (|Z ω| - δ), sq_abs (Z ω)]
    have hmul := mul_le_mul_of_nonneg_left hb (hWnonneg ω)
    nlinarith
  have hLI : Integrable (fun ω => (2 * δ) * (W ω * |Z ω|)) P :=
    hWZI.const_mul (2 * δ)
  have hRI : Integrable
      (fun ω => W ω * (Z ω)^2 + δ^2 * W ω) P :=
    hWZ2I.add (hWI.const_mul (δ^2))
  have hI := integral_mono hLI hRI hpoint
  rw [integral_const_mul] at hI
  rw [integral_add hWZ2I (hWI.const_mul (δ^2)),
      integral_const_mul, hWeightedSquare] at hI
  nlinarith
