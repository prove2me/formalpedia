-- Prove2me | solution 1 for Comp.CsgQ.castIcc_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:26:05.505814+00:00
-- url     : https://prove2.me/submissions/e4c9736a-acd5-4495-ae00-ea296836c7f4

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_ReachOp
import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Reach
import Theorems.Thm_Comp_CsgQ_castIcc_coe
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A


attribute [local simp] Comp.CsgQ.castIcc_coe

set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S : Type*}
namespace Comp.CsgQ
theorem _root_.solution (h0 : ∀ s, (0 : ℚ) ≤ (fun _ : S => (1 : ℚ)) s)
    (h1 : ∀ s, (fun _ : S => (1 : ℚ)) s ≤ 1) :
    castIcc (fun _ : S => (1 : ℚ)) h0 h1 = ⊤ := by
  funext s
  exact Subtype.ext (by simp)
end Comp.CsgQ
