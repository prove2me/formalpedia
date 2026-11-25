-- Prove2me | solution 1 for Formalism.L2.Col.BiPair.formOf_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:06:28.696411+00:00
-- url     : https://prove2.me/submissions/5b3bbb3c-7a61-42bb-acc4-1391b1ff8216

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas

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
open Formalism.L2.Col.BiPair
variable {S S' : GSD K} (P : BiPair S S')
namespace Formalism.L2.Col.BiPair
theorem _root_.solution (h' : S'.Ok) (s' : S'.Sec) (φ : S.EqFun) (ψ : S'.EqFun) :
    P.formOf h' s' φ ψ = P.sumOf h' s' φ ψ := rfl
end Formalism.L2.Col.BiPair
