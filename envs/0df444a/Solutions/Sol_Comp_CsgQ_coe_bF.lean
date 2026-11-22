-- Prove2me | solution 1 for Comp.CsgQ.coe_bF
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:08:21.584197+00:00
-- url     : https://prove2.me/submissions/44842f4b-e04a-4c5c-afe0-c0b8242c5f07

import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_Reach
import Definitions.Def_Csg_QualitativeLimitSure
import Definitions.Def_Comp_QualitativeLimitFinset
import Theorems.Thm_Comp_CsgQ_toCSG_support
import Theorems.Thm_Comp_CsgQ_mem_aF
import Theorems.Thm_Comp_CsgQ_mem_bF
import Theorems.Thm_Comp_CsgQ_castIcc_coe
import Theorems.Thm_Comp_CsgQ_coe_supportF
import Theorems.Thm_Comp_CsgQ_mem_gStepF
import Theorems.Thm_Comp_CsgQ_mem_pre1F
import Theorems.Thm_Comp_CsgQ_mem_supportF
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
attribute [local simp] Comp.CsgQ.castIcc_coe
attribute [local simp] Comp.CsgQ.coe_supportF
attribute [local simp] Comp.CsgQ.mem_gStepF
attribute [local simp] Comp.CsgQ.mem_pre1F
attribute [local simp] Comp.CsgQ.mem_supportF
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A


attribute [local simp] Comp.CsgQ.mem_aF
attribute [local simp] Comp.CsgQ.mem_bF

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq S] [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed) (v1 : Finset A1) (x : Finset S) (s : S) :
    (↑(G.bF v1 x s) : Set A2) = (G.toCSG h).B ↑v1 ↑x s := by
  have hne : ∀ a1 : A1, ∀ a2 : A2,
      ((↑(G.supportF s a1 a2) : Set S) ∩ ↑x).Nonempty
        ↔ (G.supportF s a1 a2 ∩ x).Nonempty := by
    intro a1 a2
    rw [← Finset.coe_inter, Finset.coe_nonempty]
  ext a2
  simp only [Finset.mem_coe, mem_bF, CSG.B, Set.mem_setOf_eq, toCSG_support G h]
  exact exists_congr fun a1 => and_congr_right fun _ => (hne a1 a2).symm
end Comp.CsgQ
