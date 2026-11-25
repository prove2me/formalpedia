-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.theorem_S_ring
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:34:23.139684+00:00
-- url     : https://prove2.me/submissions/c7ea9854-16be-4b66-9273-a3ea62668884

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsPFSum
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConnectionRaisingConstantEq
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sb_main
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sn_main
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_sc_main
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_relIsCoreNorm
import Theorems.Thm_Formalism_FourierDecayAlt_P_NFx2_thmSOfSteps
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_nrmFacts
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_realPoints
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_rhoUp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_tyComplete
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_tyInterlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_wExact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Polynomial
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.NF.ThmSRing :=
  NFx2.thmSOfSteps Mx3.tyInterlaces Mx3.tyComplete Mx3.rhoUp Mx3.nrmFacts Mx3.realPoints Mx3.wExact
    NFx2.sb_main NFx2.sc_main NFx2.sn_main NFx2.relIsCoreNorm
end Formalism.FourierDecayAlt.P
