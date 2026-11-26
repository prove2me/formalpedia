-- Prove2me | solution 1 for ContinuousLinearMap.intervalIntegral_mono_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:19:10.329524+00:00
-- url     : https://prove2.me/submissions/4d8ace06-e30f-41b9-b76c-2bd2d4d0dae4

import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Operator_Crouzeix_PositiveIntegral
import Theorems.Thm_ContinuousLinearMap_integral_mono_ae

set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
universe u v
open ContinuousLinearMap
variable {X : Type u} {E : Type v} [MeasurableSpace X] {μ : Measure X}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
namespace ContinuousLinearMap
theorem _root_.solution (f g : ℝ → E →L[ℂ] E) {a b : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hg : IntervalIntegrable g volume a b)
    (hfg : f ≤ᵐ[volume.restrict (Set.Ioc a b)] g) :
    (∫ x in a..b, f x) ≤ ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  exact integral_mono_ae f g
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hf)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hg) hfg
end ContinuousLinearMap
