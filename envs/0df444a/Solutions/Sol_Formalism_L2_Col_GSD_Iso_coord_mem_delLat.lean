-- Prove2me | solution 1 for Formalism.L2.Col.GSD.Iso.coord_mem_delLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:09:48.577333+00:00
-- url     : https://prove2.me/submissions/ddb7066c-af67-4a42-8be4-30c96a68b76b

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_coordOf_mem_delLat
import Theorems.Thm_Formalism_L2_Col_GSD_Iso_mem_intDel
import Theorems.Thm_Formalism_L2_Col_GSD_mem_intDel


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
theorem _root_.solution (h : S.Ok) (h' : S'.Ok) (s : S.Sec) (s' : S'.Sec) (x : Fin (S.toCSDOf h s).dim → K) :
    e.coord h h' s s' x ∈ (S'.toCSDOf h' s').delLat ↔ x ∈ (S.toCSDOf h s).delLat := by
  show S'.coordOf h' s' (e.onForms ((S.coordOf h s).symm x)) ∈ _ ↔ _
  rw [S'.coordOf_mem_delLat h' s', e.mem_intDel, ← S.coordOf_mem_delLat h s, LinearEquiv.apply_symm_apply]
end Formalism.L2.Col.GSD.Iso
