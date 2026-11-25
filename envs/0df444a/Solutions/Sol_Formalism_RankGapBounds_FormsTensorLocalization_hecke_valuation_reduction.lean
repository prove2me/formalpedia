-- Prove2me | solution 1 for Formalism.RankGapBounds.FormsTensorLocalization.hecke_valuation_reduction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:22:03.090721+00:00
-- url     : https://prove2.me/submissions/7bb6a367-9d63-4b31-a019-c0c1849b26ae

import Definitions.Def_Formalism_RankGapBounds_TheoremALocOfLemmaA
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization

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
theorem _root_.solution : HeckeValStep := by
  classical
  intro G₁ G₂ _ _ K₁ k _ W _ _ U f φ hφ g
  unfold hActK
  rw [finsum_def]
  split_ifs with h
  · exact Submodule.sum_mem _ fun x _ => Submodule.smul_mem _ _ (hφ _)
  · exact U.zero_mem
end Formalism.RankGapBounds.FormsTensorLocalization
