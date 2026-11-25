-- Prove2me | solution 1 for Formalism.L2.Col.GSD.tw_dim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:11:46.151361+00:00
-- url     : https://prove2.me/submissions/b9c9f78a-299b-4816-8999-ee5a4f1ed222

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_finrank_EqFun
import Theorems.Thm_Formalism_L2_Col_GSD_tw_finrank

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GSD
variable (K)
namespace Formalism.L2.Col.GSD
theorem _root_.solution : ((tw K).toCSD (tw_ok K)).dim = 1 := by
  exact ((tw K).finrank_EqFun (tw_ok K) (tw K).outSec).symm.trans (tw_finrank K)
end Formalism.L2.Col.GSD
