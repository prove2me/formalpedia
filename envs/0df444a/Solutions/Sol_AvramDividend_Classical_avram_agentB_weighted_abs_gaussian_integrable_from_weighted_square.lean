-- Prove2me | solution 1 for AvramDividend.Classical.avram_agentB_weighted_abs_gaussian_integrable_from_weighted_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:11:21.728984+00:00
-- url     : https://prove2.me/submissions/00bd16d3-00ad-4cda-83b9-bb06b2fda148

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false
/-- Nonnegative original Gaussian dividend-weight times absolute
source increment inherits L1 from the exact weighted square energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (W Z : Ω → ℝ)
    (hWnonneg : ∀ ω, 0 ≤ W ω)
    (hWI : Integrable W P)
    (hWZ2I : Integrable (fun ω => W ω * (Z ω)^2) P)
    (hWZabsMeas : AEStronglyMeasurable
      (fun ω => W ω * |Z ω|) P) :
    Integrable (fun ω => W ω * |Z ω|) P := by
  have hUB : Integrable (fun ω => W ω * (Z ω)^2 + W ω) P :=
    hWZ2I.add hWI
  have hPositive : ∀ᵐ ω ∂P, 0 ≤ W ω * |Z ω| := by
    exact Filter.Eventually.of_forall (fun ω => mul_nonneg (hWnonneg ω) (abs_nonneg _))
  have hBound : ∀ᵐ ω ∂P,
      W ω * |Z ω| ≤ W ω * (Z ω)^2 + W ω := by
    apply Filter.Eventually.of_forall
    intro ω
    have hScalar : |Z ω| ≤ (Z ω)^2 + 1 := by
      have hSq := sq_nonneg (|Z ω| - 1)
      nlinarith [sq_abs (Z ω), abs_nonneg (Z ω)]
    have hMult := mul_le_mul_of_nonneg_left hScalar (hWnonneg ω)
    nlinarith
  exact hUB.mono_nonneg hWZabsMeas hPositive hBound
