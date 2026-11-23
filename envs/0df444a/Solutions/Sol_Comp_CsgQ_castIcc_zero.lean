-- Prove2me | solution 1 for Comp.CsgQ.castIcc_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:25:25.54781+00:00
-- url     : https://prove2.me/submissions/a0b02875-5d0a-4dbf-b669-d65fe03f9d0c

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
theorem _root_.solution (h0 : ∀ s, (0 : ℚ) ≤ (fun _ : S => (0 : ℚ)) s)
    (h1 : ∀ s, (fun _ : S => (0 : ℚ)) s ≤ 1) :
    castIcc (fun _ : S => (0 : ℚ)) h0 h1 = ⊥ := by
  funext s
  exact Subtype.ext (by simp)
end Comp.CsgQ
