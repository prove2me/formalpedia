-- Prove2me | solution 1 for Formalism.L2.Col.ClsKer.resOf_opOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:06:55.225458+00:00
-- url     : https://prove2.me/submissions/3e73caa5-e961-4f90-8824-fdc026dd8732

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
open Formalism.L2.Col.ClsKer
variable {S S' : GSD K} (A : ClsKer S S')
namespace Formalism.L2.Col.ClsKer
theorem _root_.solution (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) (φ : S.EqFun) :
    (S'.resOf h' s' (A.opOf h s φ)).1 = letI := h.fintypeCl
      Formalism.ThetaLiftIndependence.kerOpM (fun c => (((S.toCSDOf h s).wt c : K))⁻¹) (A.atReps s s') (S.resOf h s φ).1 := rfl
end Formalism.L2.Col.ClsKer
