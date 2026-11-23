-- Prove2me | solution 1 for Comp.cert_true_star
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:34:44.363803+00:00
-- url     : https://prove2.me/submissions/e398138d-a30c-4a57-b5c5-ccb2d01da015

import Definitions.Def_Comp_Iterate
import Definitions.Def_Comp_TwoStateQ
import Theorems.Thm_Comp_stage_true_A
import Theorems.Thm_Comp_MatrixGameQ_toMatrixGame_A
attribute [local simp] Comp.MatrixGameQ.toMatrixGame_A



set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution :
    (twoGame.shapleyGameQ true vStar).ValueCert (vStar true) unif2 unif2 := by
  refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun j => ?_, ?_⟩, fun j => ?_, fun i => ?_⟩
  · norm_num [unif2]
  · rw [Fintype.sum_bool]; norm_num [unif2]
  · norm_num [unif2]
  · rw [Fintype.sum_bool]; norm_num [unif2]
  · rw [Fintype.sum_bool]; simp only [stage_true_A]
    cases j <;> norm_num [unif2, vStar]
  · rw [Fintype.sum_bool]; simp only [stage_true_A]
    cases i <;> norm_num [unif2, vStar]
end Comp
