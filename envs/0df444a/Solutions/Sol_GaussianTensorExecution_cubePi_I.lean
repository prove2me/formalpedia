-- Prove2me | solution 1 for GaussianTensorExecution.cubePi_I
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/9731f9f6-c02a-49c1-b024-b1a094321c79

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_cubeMap_congr
import Theorems.Thm_GaussianTensorExecution_cubeMap_comp
import Theorems.Thm_GaussianTensorExecution_mulPi_mulI

set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n : Nat) (z : Cube n) : cubePi n (cubeI n z) = cubeI n (cubePi n z) := by
  unfold cubePi cubeI
  rw [cubeMap_comp,cubeMap_comp]
  exact cubeMap_congr n _ _ mulPi_mulI z
end GaussianTensorExecution
