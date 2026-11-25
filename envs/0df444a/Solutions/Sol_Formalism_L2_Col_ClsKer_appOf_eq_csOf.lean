-- Prove2me | solution 1 for Formalism.L2.Col.ClsKer.appOf_eq_csOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:06:42.571439+00:00
-- url     : https://prove2.me/submissions/bade8b73-fc27-481d-b84f-1ed0da7db157

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
namespace Formalism.L2.Col
namespace ClsKer
theorem _root_.solution {S S' : GSD K} (A : ClsKer S S') (h : S.Ok) (s : S.Sec) (φ : S.D → S.V) (d' : S'.D) :
    A.appOf h s φ d' = S.csOf h s fun d => A.k d d' (φ d) := rfl
end ClsKer
end Formalism.L2.Col
