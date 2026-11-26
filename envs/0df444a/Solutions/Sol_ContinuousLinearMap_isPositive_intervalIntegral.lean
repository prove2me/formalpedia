-- Prove2me | solution 1 for ContinuousLinearMap.isPositive_intervalIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:45:00.294292+00:00
-- url     : https://prove2.me/submissions/353cbe73-ec07-4084-9799-80e6fbac4bc7

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
theorem _root_.solution (f : ℝ → E →L[ℂ] E) {a b : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hpos : ∀ᵐ x ∂volume.restrict (Set.Ioc a b), IsPositive (f x)) :
    IsPositive (∫ x in a..b, f x) := by
  rw [intervalIntegral.integral_of_le hab]
  exact isPositive_integral f
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf) hpos
end ContinuousLinearMap
