-- Prove2me | solution 1 for Comp.rps_valueCert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:32:20.759182+00:00
-- url     : https://prove2.me/submissions/e76de0ed-be90-49a3-9dc0-cabac190efc3

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Comp_RockPaperScissorsQ
import Theorems.Thm_Csg_rpsAction_sum


set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution : rpsMatrixQ.ValueCert 0 rpsUnif rpsUnif := by
  refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun j => ?_, ?_⟩, fun j => ?_, fun i => ?_⟩
  · norm_num [rpsUnif]
  · rw [rpsAction_sum]; norm_num [rpsUnif]
  · norm_num [rpsUnif]
  · rw [rpsAction_sum]; norm_num [rpsUnif]
  · rw [rpsAction_sum]; cases j <;> norm_num [rpsUnif, rpsMatrixQ, rpsPayoffQ]
  · rw [rpsAction_sum]; cases i <;> norm_num [rpsUnif, rpsMatrixQ, rpsPayoffQ]
end Comp
