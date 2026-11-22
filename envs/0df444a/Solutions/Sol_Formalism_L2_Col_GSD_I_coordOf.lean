-- Prove2me | solution 1 for Formalism.L2.Col.GSD.I_coordOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:07:15.193463+00:00
-- url     : https://prove2.me/submissions/5afc0b22-fe07-4c4f-b11e-b1122dbd035e

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
namespace Formalism.L2.Col.GSD
theorem _root_.solution (h : S.Ok) (s : S.Sec) (φ : S.EqFun) :
    (S.toCSDOf h s).I (S.coordOf h s φ) = fun c => (φ : S.D → S.V) (s.rep c) := by
  show (((S.toCSDOf h s).basis.equivFun.symm ((S.toCSDOf h s).basis.equivFun (S.resOf h s φ)) :
    (S.toCSDOf h s).Forms) : S.Cl → S.V) = _
  rw [LinearEquiv.symm_apply_apply]
  rfl
end Formalism.L2.Col.GSD
