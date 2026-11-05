-- Prove2me | solution 1 for GaussianTensorExecution.cubePiIter_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/6ce6202f-c7cd-4183-86e1-3c52ac81347b

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_cubeMap_congr
import Theorems.Thm_GaussianTensorExecution_cubeMap_comp
import Theorems.Thm_GaussianParity_piIter_add


set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (k l n : Nat) (z : Cube n) :
    cubePiIter (k+l) n z = cubePiIter k n (cubePiIter l n z) := by
  unfold cubePiIter
  rw [cubeMap_comp]
  exact cubeMap_congr n _ _ (piIter_add k l) z
end GaussianTensorExecution
