-- Prove2me | solution 1 for ContinuousLinearMap.contourIntegral_comp_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:29:53.152823+00:00
-- url     : https://prove2.me/submissions/c3f3826a-4623-4c28-8340-9f593ee2b6a6

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Definitions.Def_Operator_Crouzeix_ContourIntegral

set_option autoImplicit false
open scoped Real Interval
open MeasureTheory Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
namespace ContinuousLinearMap
theorem _root_.solution [CompleteSpace F] [CompleteSpace G]
    (L : F →L[ℂ] G)
    {f : ℂ → F} {γ : ℝ → ℂ} (hf : ContourIntegrable f γ) :
    contourIntegral (fun z => L (f z)) γ = L (contourIntegral f γ) := by
  unfold contourIntegral
  simpa only [Function.comp_apply, map_smul] using L.intervalIntegral_comp_comm hf
end ContinuousLinearMap
