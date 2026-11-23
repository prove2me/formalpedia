-- Prove2me | solution 1 for Comp.CsgQ.reachOp_coe_of_valueCert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:26:09.516855+00:00
-- url     : https://prove2.me/submissions/b8192718-7012-44e8-80a2-15f1d3fedb4e

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Reach
import Theorems.Thm_Comp_CsgQ_reachGameQ_stageValue
import Theorems.Thm_Comp_CsgQ_reachOp_coe
import Theorems.Thm_Comp_MatrixGameQ_value_eq_of_valueCert


set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace Comp.CsgQ
theorem _root_.solution (G : CsgQ S A1 A2) (h : G.WellFormed)
    (hr0 : ∀ s a1 a2, G.r s a1 a2 = 0) (goal : S → Prop) [DecidablePred goal]
    (v : S → ℚ) (h0 : ∀ s, 0 ≤ v s) (h1 : ∀ s, v s ≤ 1) {s : S} {t : ℚ}
    {p : A1 → ℚ} {q : A2 → ℚ} (hs : ¬ goal s)
    (hc : (G.reachGameQ s v).ValueCert t p q) :
    ((((G.toCSG h).reachOp goal (toCSG_r_zero G h hr0)) (castIcc v h0 h1) s : ℝ))
      = ((t : ℚ) : ℝ) := by
  rw [reachOp_coe, if_neg hs, reachGameQ_stageValue G h hr0 s v h0 h1]
  exact MatrixGameQ.value_eq_of_valueCert hc
end Comp.CsgQ
