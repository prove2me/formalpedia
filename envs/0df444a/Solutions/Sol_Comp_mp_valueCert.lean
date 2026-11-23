-- Prove2me | solution 1 for Comp.mp_valueCert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:33:23.8838+00:00
-- url     : https://prove2.me/submissions/aa66b89d-9d77-4895-8ce3-d34ba1e0522c

import Definitions.Def_Comp_Shapley
import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Comp_RockPaperScissorsQ

set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg
namespace Comp
theorem _root_.solution : mpMatrixQ.ValueCert 0 mpUnif mpUnif := by
  refine ⟨⟨fun i => ?_, ?_⟩, ⟨fun j => ?_, ?_⟩, fun j => ?_, fun i => ?_⟩
  · norm_num [mpUnif]
  · rw [Fintype.sum_bool]; norm_num [mpUnif]
  · norm_num [mpUnif]
  · rw [Fintype.sum_bool]; norm_num [mpUnif]
  · rw [Fintype.sum_bool]; cases j <;> norm_num [mpUnif, mpMatrixQ, mpPayoffQ]
  · rw [Fintype.sum_bool]; cases i <;> norm_num [mpUnif, mpMatrixQ, mpPayoffQ]
end Comp
