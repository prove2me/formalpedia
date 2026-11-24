-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.weight_reflection_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:03:05.730329+00:00
-- url     : https://prove2.me/submissions/145e800f-0988-47d9-994a-07e619cfc7a1

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent
namespace Formalism.CohomologicalDescent.WorkedExample
theorem _root_.solution : MwFlip := by
  intro l b h t κ U
  unfold mwCount
  apply Finset.card_bij' (fun u _ => h - u) (fun u _ => h - u)
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc] at hu ⊢
    obtain ⟨⟨⟨w, hw, rfl⟩, hB⟩, x, hx, hxu⟩ := hu
    refine ⟨⟨by simpa using hw, fun hc => hB ⟨by omega, by omega⟩⟩, h - x, ⟨by omega, by omega⟩, ?_⟩
    exact (Int.ModEq.refl h).sub hxu
  · intro u hu
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Icc] at hu ⊢
    obtain ⟨⟨hw, hB⟩, x, hx, hxu⟩ := hu
    refine ⟨⟨⟨u, hw, rfl⟩, fun hc => hB ⟨by omega, by omega⟩⟩, h - x, ⟨by omega, by omega⟩, ?_⟩
    exact (Int.ModEq.refl h).sub hxu
  · intro u _; ring
  · intro u _; ring
end Formalism.CohomologicalDescent.WorkedExample
