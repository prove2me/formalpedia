-- Prove2me | solution 1 for Formalism.L2.Col.LocOp.adjoint_of_nondeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:12:10.99109+00:00
-- url     : https://prove2.me/submissions/11c6522f-589e-4548-9ccb-59291030624b

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_LocOp_ker_eq_zero_iff
import Theorems.Thm_Formalism_L2_Col_LocOp_adjoint

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
open Formalism.L2.Col.LocOp
variable {S S' : GSD K}
namespace Formalism.L2.Col.LocOp
theorem _root_.solution (A : LocOp S S') (B : LocOp S' S) (h : S.Ok) (h' : S'.Ok) (e : S.G ≃* S'.G)
    (hB : ∀ g, B.tr g = e g) (hn : S.pair.Nondegenerate)
    (hn' : S'.pair.Nondegenerate)
    (hadj : ∀ d d' x y, S'.pair (A.ker d' d x) y = S.pair x (B.ker d d' y))
    (s : S.Sec) (s' : S'.Sec) (φ : S.EqFun) (ψ : S'.EqFun) :
    S'.ipOf h' s' (A.app φ) ψ = S.ipOf h s φ (B.app ψ) := by
  exact A.adjoint B h h' e hB (fun d d' => A.ker_eq_zero_iff B hn hn' hadj d d') hadj s s' φ ψ
end Formalism.L2.Col.LocOp
