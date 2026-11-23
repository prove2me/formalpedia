-- Prove2me | solution 1 for Comp.cert_false_v1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:35:50.137377+00:00
-- url     : https://prove2.me/submissions/e51baf2e-bb8e-470b-8e59-9d6f343afb59

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
    (twoGame.shapleyGameQ false v1).ValueCert (v2 false) pure2 pure2 := by
  refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun j => ?_, ?_⟩, fun j => ?_, fun i => ?_⟩
  · cases i <;> norm_num [pure2]
  · rw [Fintype.sum_bool]; norm_num [pure2]
  · cases j <;> norm_num [pure2]
  · rw [Fintype.sum_bool]; norm_num [pure2]
  · rw [Fintype.sum_bool]; simp only [stage_false_A]
    norm_num [pure2, v1, v2]
  · rw [Fintype.sum_bool]; simp only [stage_false_A]
    norm_num [pure2, v1, v2]
end Comp
