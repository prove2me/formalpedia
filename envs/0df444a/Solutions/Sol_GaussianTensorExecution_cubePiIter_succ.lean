-- Prove2me | solution 1 for GaussianTensorExecution.cubePiIter_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/f1bd249c-bd66-4465-aa4c-09869f56eba5

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_cubeMap_comp

set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (k n : Nat) (z : Cube n) :
    cubePiIter (k+1) n z = cubePi n (cubePiIter k n z) := by
  unfold cubePiIter cubePi
  rw [cubeMap_comp]
  rfl
end GaussianTensorExecution
