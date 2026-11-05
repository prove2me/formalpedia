-- Prove2me | solution 1 for GaussianTensorExecution.axis_inverse_forward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/e6178713-df58-4a91-8d7e-9d367321f37d

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_cube_ext
import Theorems.Thm_GaussianTensorExecution_get_map
import Theorems.Thm_GaussianTensorExecution_get_zip
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n : Nat) (z : Cube n × Cube n) :
    axisInverse n (axisForward n z) =
      (cubePiIter 2 n z.1,cubePiIter 2 n z.2) := by
  apply Prod.ext <;> apply cube_ext n <;> intro p
  · simp only [axisInverse,axisForward,cubeAdd,cubeI,cubePiIter,get_map,get_zip]
    apply GInt.ext <;> simp only [add,mulI,piIter,mulPi] <;> omega
  · simp only [axisInverse,axisForward,cubeAdd,cubeI,cubePiIter,get_map,get_zip]
    apply GInt.ext <;> simp only [add,mulI,piIter,mulPi] <;> omega
end GaussianTensorExecution
