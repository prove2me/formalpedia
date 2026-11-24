-- Prove2me | solution 1 for Formalism.CohomologicalDescent.WorkedExample.weight_letters_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:13:19.981795+00:00
-- url     : https://prove2.me/submissions/8a77fe75-21bc-4bdc-942f-197bd170dd85

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_weight_reflection_holds

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
theorem _root_.solution : MwLetters := by
  intro ι N D σ h t hR l κ i
  obtain ⟨_, _, _, hU, _, hbot⟩ := hR
  unfold Labels.mw
  have himg : Finset.univ.image (D.U (D.cc i)) =
      (Finset.univ.image (D.U i)).image (fun u => (h : ℤ) - u) := by
    ext w
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨D.U i (Fin.rev a), ⟨_, rfl⟩, (hU i a).symm⟩
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨Fin.rev a, by rw [hU, Fin.rev_rev]⟩
  rw [himg, hbot]
  exact weight_reflection_holds l (D.bot i) h t κ _
end Formalism.CohomologicalDescent.WorkedExample
