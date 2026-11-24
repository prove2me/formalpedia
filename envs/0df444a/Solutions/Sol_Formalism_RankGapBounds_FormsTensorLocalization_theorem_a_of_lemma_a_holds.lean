-- Prove2me | solution 1 for Formalism.RankGapBounds.FormsTensorLocalization.theorem_a_of_lemma_a_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:42:44.342971+00:00
-- url     : https://prove2.me/submissions/e541226d-8de0-4b3a-a58e-20a9a6ec0de0

import Definitions.Def_Formalism_RankGapBounds_TheoremALocOfLemmaA
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Theorems.Thm_Formalism_RankGapBounds_FormsTensorLocalization_tensor_reduction_holds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct
open Formalism Formalism.RankGapBounds Formalism.RankGapBounds.FormsTensorLocalization
open Formalism.UG
namespace Formalism.RankGapBounds.FormsTensorLocalization
theorem _root_.solution : TheoremA_of_LemmaA := by
  intro G _ Γ K k _ ι _ A _ _ B ρK l e hB f hf
  refine Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ hf, Submodule.mem_pi.2 fun g _ => ?_⟩
  exact tensor_reduction_holds k ι A B l e hB (f g)
end Formalism.RankGapBounds.FormsTensorLocalization
