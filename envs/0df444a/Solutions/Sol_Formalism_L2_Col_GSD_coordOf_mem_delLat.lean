-- Prove2me | solution 1 for Formalism.L2.Col.GSD.coordOf_mem_delLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:18:48.961714+00:00
-- url     : https://prove2.me/submissions/d6123bb4-17a6-42ba-b146-cbf4a6f32dc4

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas
import Theorems.Thm_Formalism_L2_Col_GSD_mem_intDel_iff
import Theorems.Thm_Formalism_L2_Col_GSD_I_coordOf

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
    S.coordOf h s φ ∈ (S.toCSDOf h s).delLat ↔ φ ∈ S.intDel := by
  unfold CSD.delLat valLatF
  rw [Submodule.mem_comap, LinearMap.restrictScalars_apply, S.I_coordOf h s φ, Submodule.mem_pi, S.mem_intDel_iff h s φ]
  exact ⟨fun H c => H c (Set.mem_univ c), fun H c _ => H c⟩
end Formalism.L2.Col.GSD
