-- Prove2me | solution 1 for Formalism.REAL.compact_haar_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:57:48.060795+00:00
-- url     : https://prove2.me/submissions/1f8d6005-033a-4c11-884c-0636ead48152

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactHaarRightInvariantInst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory MeasureTheory.Measure
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution : KHaar := by
  intro n ε
  haveI : IsMulLeftInvariant (muK ε) := by
    unfold muK
    infer_instance
  refine ⟨compact_haar_probability n ε, fun k => map_mul_left_eq_self _ k, fun k => compact_haar_right_invariant n ε k, ?_⟩
  haveI : IsProbabilityMeasure (Measure.map (fun x : KG ε => x⁻¹) (muK ε)) :=
    isProbabilityMeasure_map measurable_inv.aemeasurable
  haveI : IsMulLeftInvariant (Measure.map (fun x : KG ε => x⁻¹) (muK ε)) := by
    constructor
    intro g
    rw [Measure.map_map (measurable_const_mul g) measurable_inv]
    have e : ((g * ·) ∘ (fun x : KG ε => x⁻¹)) = ((fun x : KG ε => x⁻¹) ∘ (· * g⁻¹)) := by
      funext x
      simp
    rw [e, ← Measure.map_map measurable_inv (measurable_mul_const g⁻¹), compact_haar_right_invariant]
  exact compact_haar_unique_left _
end Formalism.REAL
