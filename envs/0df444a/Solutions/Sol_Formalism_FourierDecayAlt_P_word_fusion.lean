-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.word_fusion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:49:15.77275+00:00
-- url     : https://prove2.me/submissions/04827919-30ca-4573-b723-9c97a2916828

import Definitions.Def_Formalism_HermitianCurvature_StatementW
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Theorems.Thm_Formalism_FourierDecayAlt_P_W_wordFusion_list

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open NumberField
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.W.WordFusion := by
  unfold Formalism.FourierDecayAlt.W.WordFusion
  intro R B _ _ _ L h hp
  exact Formalism.FourierDecayAlt.P.W.wordFusion_list L h hp
end Formalism.FourierDecayAlt.P
