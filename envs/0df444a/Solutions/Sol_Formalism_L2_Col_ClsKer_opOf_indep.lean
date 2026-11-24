-- Prove2me | solution 1 for Formalism.L2.Col.ClsKer.opOf_indep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:53:27.926276+00:00
-- url     : https://prove2.me/submissions/dd547c9a-bb8f-45c0-b163-97ae4cf5e980

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_ClsKer_appOf_indep

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
open Formalism.L2.Col.ClsKer
variable {S S' : GSD K} (A : ClsKer S S')
namespace Formalism.L2.Col.ClsKer
theorem _root_.solution (h : S.Ok) (s s' : S.Sec) : A.opOf h s = A.opOf h s' := by
  exact LinearMap.ext fun φ => Subtype.ext (A.appOf_indep h s s' φ)
end Formalism.L2.Col.ClsKer
