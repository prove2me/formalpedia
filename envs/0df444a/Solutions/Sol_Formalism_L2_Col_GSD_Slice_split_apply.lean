-- Prove2me | solution 1 for Formalism.L2.Col.GSD.Slice.split_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:17:26.435251+00:00
-- url     : https://prove2.me/submissions/0d8c9645-599b-428f-bd5a-38ab954f9dee

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
open Formalism.L2.Col.GSD
variable (S : GSD K)
variable (A : Type) [Group A] [MulAction A S.D]
open Formalism.L2.Col.GSD.Slice
variable {S A} (σ : S.Slice A)
variable [SMulCommClass A S.G S.D]
namespace Formalism.L2.Col.GSD.Slice
theorem _root_.solution (φ : S.EqFun) (b : A) (t : σ.T) :
    ((σ.split φ b : (S.restr σ.T).EqFun) : σ.T → S.V) t = (φ : S.D → S.V) (b • (t : S.D)) := rfl
end Formalism.L2.Col.GSD.Slice
