-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.SmOn.continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:27:47.935474+00:00
-- url     : https://prove2.me/submissions/082bb7aa-717e-4e0b-88ba-88a3422e74d9

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
variable {E E' V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace CompanionTheory.D.Upq.Sm
namespace SmOn
theorem _root_.solution {A : Set E} {f : E → V} (hf : SmOn A f) : ContinuousOn f A := by
  intro a ha
  obtain ⟨U, F, hU, haU, hF, hfF⟩ := hf a ha
  have h1 : ContinuousWithinAt F A a :=
    (hF.continuousOn.continuousAt (hU.mem_nhds haU)).continuousWithinAt
  refine h1.congr_of_eventuallyEq ?_ (hfF a haU ha)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds haU), self_mem_nhdsWithin] with g h1 h2
  exact hfF g h1 h2
end SmOn
end CompanionTheory.D.Upq.Sm
