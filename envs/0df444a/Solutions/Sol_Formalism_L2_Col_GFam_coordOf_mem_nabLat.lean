-- Prove2me | solution 1 for Formalism.L2.Col.GFam.coordOf_mem_nabLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:07:17.232194+00:00
-- url     : https://prove2.me/submissions/e251fd55-d7a6-45d5-a295-c95ecbe4ee6d

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_mem_intNab_iff
import Theorems.Thm_Formalism_L2_Col_GSD_I_coordOf
import Theorems.Thm_Formalism_L2_Col_GSD_Iso_mem_intNab
import Theorems.Thm_Formalism_L2_Col_GFam_mem_intNab
import Theorems.Thm_Formalism_L2_Col_GFam_I_coordOf
import Theorems.Thm_Formalism_L2_Col_GSD_mem_intNab


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
    F.coordOf h s φ ∈ (F.toCSDOf h s).nabLat ↔ φ ∈ F.intNab := by
  unfold CSD.nabLat valLatF
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, F.I_coordOf h s φ, Submodule.mem_pi, F.mem_intNab]
  simp only [Set.mem_univ, true_implies, Sigma.forall]
  exact forall_congr' fun b => ((F.mem b).mem_intNab_iff (h b) (s b) (φ b)).symm
end Formalism.L2.Col.GFam
