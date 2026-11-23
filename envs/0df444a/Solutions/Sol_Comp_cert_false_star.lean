-- Prove2me | solution 1 for Comp.cert_false_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:34:51.201986+00:00
-- url     : https://prove2.me/submissions/63bfe7bc-3ed7-462e-bb4f-29a5c20dc8e0

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_TwoStateQ
import Theorems.Thm_Comp_stage_false_A
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A



set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution :
    (twoGame.shapleyGameQ false vStar).ValueCert (vStar false) pure2 pure2 := by
  refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun j => ?_, ?_⟩, fun j => ?_, fun i => ?_⟩
  · cases i <;> norm_num [pure2]
  · rw [Fintype.sum_bool]; norm_num [pure2]
  · cases j <;> norm_num [pure2]
  · rw [Fintype.sum_bool]; norm_num [pure2]
  · rw [Fintype.sum_bool]; simp only [stage_false_A]
    norm_num [pure2, vStar]
  · rw [Fintype.sum_bool]; simp only [stage_false_A]
    norm_num [pure2, vStar]
end Comp
