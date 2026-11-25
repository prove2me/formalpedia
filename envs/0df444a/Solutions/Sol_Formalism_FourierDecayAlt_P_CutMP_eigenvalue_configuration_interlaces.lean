-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.eigenvalue_configuration_interlaces
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:51:59.58111+00:00
-- url     : https://prove2.me/submissions/6f55c457-64ea-4290-9a91-cb783aff095c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutMP2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutLam
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_cfg_interlaces

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
namespace Formalism.FourierDecayAlt.P.CutMP
theorem _root_.solution : LamCfgInterlaces := by
  intro E _ _ _ Wp Wq _ _ _ _ S hk hok hw hw' v
  exact ⟨cfg_interlaces (S.G.place (S.pl v)) S.G.r rfl hk (hok v) S.de hw.1,
    cfg_interlaces (S.G.place (S.pl v)) S.G.r rfl hk (hok v) S.de' hw'.1⟩
end Formalism.FourierDecayAlt.P.CutMP
