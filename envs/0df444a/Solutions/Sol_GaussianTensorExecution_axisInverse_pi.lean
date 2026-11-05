-- Prove2me | solution 1 for GaussianTensorExecution.axisInverse_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/204f9b7e-c1cd-459a-b208-6e409d42e0fe

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_cubePi_add
import Theorems.Thm_GaussianTensorExecution_cubePi_I
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n : Nat) (z : Cube n × Cube n) :
    axisInverse n (cubePi n z.1,cubePi n z.2) =
      (cubePi n (axisInverse n z).1,cubePi n (axisInverse n z).2) := by
  apply Prod.ext <;> simp only [axisInverse,cubePi_add,cubePi_I]
end GaussianTensorExecution
