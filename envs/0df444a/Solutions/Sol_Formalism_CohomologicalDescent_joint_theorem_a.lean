-- Prove2me | solution 1 for Formalism.CohomologicalDescent.joint_theorem_a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:27:31.461286+00:00
-- url     : https://prove2.me/submissions/ea7203e7-329a-4b8b-9917-eee2fbdcdc06

import Definitions.Def_Formalism_PieriBlockIdeals_JointTheoremALoc
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ExactExponentLatticeIncl
import Theorems.Thm_Formalism_CohomologicalDescent_exact_exponent_lattice_incl
import Theorems.Thm_Formalism_RankGapBounds_FormsTensorLocalization_theorem_a_of_lemma_a_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CohomologicalDescent
open TensorProduct Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization
namespace Formalism.CohomologicalDescent
theorem _root_.solution : JointTheoremA := by
  intro G _ Γ K k _ ι _ A _ _ B ρK l hex
  have h := theorem_a_of_lemma_a_holds G Γ K k ι A B ρK l (fun i => exactExp l (B i))
    (fun i => exact_exponent_lattice_incl l (B i) (hex i))
  exact ⟨h, Nat.sInf_le h⟩
end Formalism.CohomologicalDescent
