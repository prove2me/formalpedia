-- Prove2me | solution 1 for Formalism.L2.Col.GFam.coordOf_mem_delLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:12:38.447913+00:00
-- url     : https://prove2.me/submissions/f4abbafb-e6bb-4c3b-8953-35d9ba36a6c9

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_mem_intDel_iff
import Theorems.Thm_Formalism_L2_Col_GSD_I_coordOf
import Theorems.Thm_Formalism_L2_Col_GSD_Iso_mem_intDel
import Theorems.Thm_Formalism_L2_Col_GFam_mem_intDel
import Theorems.Thm_Formalism_L2_Col_GFam_I_coordOf
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
open Formalism.L2.Col.GFam
variable (F : GFam K)
namespace Formalism.L2.Col.GFam
theorem _root_.solution (h : F.Ok) (s : ∀ b, (F.mem b).Sec) (φ : F.Forms) :
    F.coordOf h s φ ∈ (F.toCSDOf h s).delLat ↔ φ ∈ F.intDel := by
  unfold CSD.delLat valLatF
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, F.I_coordOf h s φ, Submodule.mem_pi, F.mem_intDel]
  simp only [Set.mem_univ, true_implies, Sigma.forall]
  exact forall_congr' fun b => ((F.mem b).mem_intDel_iff (h b) (s b) (φ b)).symm
end Formalism.L2.Col.GFam
