-- Prove2me | solution 1 for Comp.CsgQ.reachGameQ_stageValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T23:28:09.65833+00:00
-- url     : https://prove2.me/submissions/cc870560-418f-499f-892d-c6fc1656be94

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Reach
import Theorems.Thm_Comp_CsgQ_castIcc_coe
import Theorems.Thm_Comp_CsgQ_reachGameQ_A_cast
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
import Theorems.Thm_Csg_MatrixGame_abs_value_sub_le
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A


attribute [local simp] Comp.CsgQ.castIcc_coe

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (s : S) (v : S → ℚ)
    (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) :
    (G.toCSG h).stageValue s (fun s' => ((castIcc v h0 h1 s' : ℝ)))
      = (G.reachGameQ s v).toMatrixGame.value := by
  change ((G.toCSG h).stageGame s (fun s' => ((castIcc v h0 h1 s' : ℝ)))).value = _
  have hb : |((G.toCSG h).stageGame s (fun s' => ((castIcc v h0 h1 s' : ℝ)))).value
      - (G.reachGameQ s v).toMatrixGame.value| ≤ 0 :=
    MatrixGame.abs_value_sub_le (ε := 0) fun a1 a2 => by
      rw [reachGameQ_A_cast G h hr0 s v h0 h1 a1 a2]
      simp
  have hz := abs_nonpos_iff.mp hb
  linarith
end Comp.CsgQ
