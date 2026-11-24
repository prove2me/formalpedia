-- Prove2me | solution 1 for Formalism.L2.Col.GSD.Iso.hform_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:02:22.054876+00:00
-- url     : https://prove2.me/submissions/28ab4845-74ab-438f-bfb4-c4c266e33414

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_ipOf_coord
import Theorems.Thm_Formalism_L2_Col_GSD_Iso_ipOf_onForms

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
open Formalism.L2.Col.GSD Formalism.L2.Col.GSD.Iso
variable {S S' : GSD K} (e : GSD.Iso S S')
namespace Formalism.L2.Col.GSD.Iso
theorem _root_.solution (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) (x y : Fin (S.toCSDOf h s).dim → K) :
    hform (S'.toCSDOf h' s').H (e.coord h h' s s' x) (e.coord h h' s s' y) = hform (S.toCSDOf h s).H x y := by
  have e1 := S'.ipOf_coord h' s' (e.onForms ((S.coordOf h s).symm x)) (e.onForms ((S.coordOf h s).symm y))
  have e2 := S.ipOf_coord h s ((S.coordOf h s).symm x) ((S.coordOf h s).symm y)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e2
  rw [e.ipOf_onForms h h' s s'] at e1
  exact e1.symm.trans e2
end Formalism.L2.Col.GSD.Iso
