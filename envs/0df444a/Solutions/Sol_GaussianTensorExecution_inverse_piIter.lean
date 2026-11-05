-- Prove2me | solution 1 for GaussianTensorExecution.inverse_piIter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/59f6ae3f-deb5-4e0e-b6c3-575163fab34a

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_inverse_pi
import Theorems.Thm_GaussianTensorExecution_cubePiIter_succ
import Theorems.Thm_GaussianTensorExecution_cubeMap_id

set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (k n : Nat) (z : Cube n) :
    inverse n (cubePiIter k n z) = cubePiIter k n (inverse n z) := by
  induction k with
  | zero => simp [cubePiIter,piIter,cubeMap_id]
  | succ k ih => rw [cubePiIter_succ,inverse_pi,ih,← cubePiIter_succ]
end GaussianTensorExecution
