-- Prove2me | solution 1 for Comp.DiscountedCsgQ.shapleyGameQ_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:46:41.949793+00:00
-- url     : https://prove2.me/submissions/9c9356fb-bfc3-431e-a57a-2ffc1044e113

import Definitions.Def_Comp_Search
import Definitions.Def_Comp_Shapley
import Theorems.Thm_Comp_DiscountedCsgQ_shapleyGameQ_A_cast
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
import Theorems.Thm_Csg_MatrixGame_abs_value_sub_le
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A



set_option autoImplicit true
open Comp
open Csg
open Comp.DiscountedCsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]
namespace Comp.DiscountedCsgQ
theorem _root_.solution (G : DiscountedCsgQ S A1 A2) (h : G.WellFormed) (s : S) (v : S → ℚ) :
    ((G.toDiscountedCSG h).shapleyGame s (fun s' => ((v s' : ℚ) : ℝ))).value
      = (G.shapleyGameQ s v).toMatrixGame.value := by
  have hb : |((G.toDiscountedCSG h).shapleyGame s (fun s' => ((v s' : ℚ) : ℝ))).value
      - (G.shapleyGameQ s v).toMatrixGame.value| ≤ 0 :=
    MatrixGame.abs_value_sub_le (ε := 0) fun a1 a2 => by
      rw [shapleyGameQ_A_cast G h s v a1 a2]
      simp
  have hz := abs_nonpos_iff.mp hb
  linarith
end Comp.DiscountedCsgQ
