-- Prove2me | solution 1 for Formalism.RankGapBounds.FormsTensorLocalization.TheoremA_loc_from_LemmaA
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:51:41.417829+00:00
-- url     : https://prove2.me/submissions/6e77374b-b1ea-462b-92ad-2a8e96912fc7

import Definitions.Def_Formalism_RankGapBounds_TheoremALocOfLemmaA
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Theorems.Thm_Formalism_RankGapBounds_FormsTensorLocalization_localization_reduction_holds
import Theorems.Thm_Formalism_RankGapBounds_FormsTensorLocalization_theorem_a_of_lemma_a_holds

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
theorem _root_.solution : TheoremA_loc_of_LemmaA := by
  intro G _ Γ K k _ ι _ A _ _ B ρK l e T _ _ _ _ S hB y
  refine localization_reduction_holds T (AMFK k Γ K ρK) S _ (algebraMap k T l) (∑ i, e i) (fun x => ?_) y
  show ((algebraMap k T l ^ (∑ i, e i) • x : AMFK k Γ K ρK) : G → ⨂[k] i, A i) ∈ formsIn Γ K ρK (tensSub B)
  rw [← map_pow, algebraMap_smul]
  exact theorem_a_of_lemma_a_holds G Γ K k ι A B ρK l e hB x x.2
end Formalism.RankGapBounds.FormsTensorLocalization
