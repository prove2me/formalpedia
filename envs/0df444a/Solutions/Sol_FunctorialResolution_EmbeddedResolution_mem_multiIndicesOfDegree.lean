-- Prove2me | solution 1 for FunctorialResolution.EmbeddedResolution.mem_multiIndicesOfDegree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:52.896266+00:00
-- url     : https://prove2.me/submissions/d591591b-da70-4d38-a245-78fd255e7c4f

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_IdealOrder
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_MultiIndexDerivation
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_DerivativeIdealOrderDecrease
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_DerivativeIdeal_LeadingForm
import Theorems.Thm_FunctorialResolution_EmbeddedResolution_unitMultiIndex_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] FunctorialResolution.EmbeddedResolution.unitMultiIndex_apply



set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open IsLocalRing
namespace FunctorialResolution.EmbeddedResolution
theorem _root_.solution {h r : ℕ} (β : Fin h → ℕ) :
    β ∈ multiIndicesOfDegree h r ↔ ∑ i, β i = r := by
  simp only [multiIndicesOfDegree, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · exact fun hβ => hβ.2
  · intro hs
    refine ⟨fun i => ?_, hs⟩
    have h1 : β i ≤ r := by
      rw [← hs]
      exact Finset.single_le_sum (f := β) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
end FunctorialResolution.EmbeddedResolution
