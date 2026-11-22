-- Prove2me | solution 1 for Formalism.L2.Col.GFam.I_coordOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:46:04.647774+00:00
-- url     : https://prove2.me/submissions/aeac6e6a-5c07-4e0b-b15d-b7c9dcba162b

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
open Formalism.L2.Col.GFam
variable (F : GFam K)
namespace Formalism.L2.Col.GFam
theorem _root_.solution (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms) :
    (F.toCSDOf h s).I (F.coordOf h s φ) = (F.resOf h s φ).1 := by
  show (((F.toCSDOf h s).basis.equivFun.symm ((F.toCSDOf h s).basis.equivFun (F.resOf h s φ)) :
    (F.toCSDOf h s).Forms) : F.Cl → F.V) = _
  rw [LinearEquiv.symm_apply_apply]
end Formalism.L2.Col.GFam
