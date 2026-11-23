-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GramProductIdentities.pairAdj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:32.219801+00:00
-- url     : https://prove2.me/submissions/c4ee5c5f-1e76-421b-925e-4c75ca364505

import Definitions.Def_Formalism_HermitianCurvature_PositionExpansionTopCoefficients
import Definitions.Def_Lemmata_HermitianSesquilinear_ConjEqOfNonnegReal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramProductIdentities
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_act_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_act_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_act_csmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_GramProductIdentities_pair_act

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GramProductIdentities
open Finset Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace Formalism.FourierDecayAlt.P.GramProductIdentities
theorem _root_.solution : PairAdj := by
  intro A S V _ _ _ _ _ _ _ _ _ ρ M N c X X'
  exact ⟨act_mul M N X, act_one X, act_csmul M c X, pair_act ρ M X X'⟩
end Formalism.FourierDecayAlt.P.GramProductIdentities
