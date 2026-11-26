-- Prove2me | solution 1 for ContinuousLinearMap.integral_mono_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:46.326099+00:00
-- url     : https://prove2.me/submissions/34aeff66-dcdc-4c1c-b5e4-c1d34c13ddb9

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
import Theorems.Thm_ContinuousLinearMap_isPositive_integral

set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
universe u v
open ContinuousLinearMap
variable {X : Type u} {E : Type v} [MeasurableSpace X] {μ : Measure X}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
namespace ContinuousLinearMap
theorem _root_.solution (f g : X → E →L[ℂ] E) (hf : Integrable f μ)
    (hg : Integrable g μ) (hfg : f ≤ᵐ[μ] g) :
    (∫ x, f x ∂μ) ≤ ∫ x, g x ∂μ := by
  rw [ContinuousLinearMap.le_def, ← integral_sub hg hf]
  exact isPositive_integral (fun x => g x - f x) (hg.sub hf) hfg
end ContinuousLinearMap
