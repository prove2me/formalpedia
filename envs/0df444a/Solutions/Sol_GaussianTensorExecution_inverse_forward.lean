-- Prove2me | solution 1 for GaussianTensorExecution.inverse_forward
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/d78a2def-a93a-4c35-b7c1-8da4c2391384

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_cubePiIter_add
import Theorems.Thm_GaussianTensorExecution_cubeMap_id
import Theorems.Thm_GaussianTensorExecution_inverse_piIter
import Theorems.Thm_GaussianTensorExecution_axis_inverse_forward
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n : Nat) (z : Cube n) :
    inverse n (forward n z) = cubePiIter (2*n) n z := by
  induction n with
  | zero => simp [inverse,forward,cubePiIter,piIter,cubeMap_id]
  | succ n ih =>
    change
      (inverse n (axisInverse n (axisForward n (forward n z.1,forward n z.2))).1,
       inverse n (axisInverse n (axisForward n (forward n z.1,forward n z.2))).2) =
      (cubePiIter (2*(n+1)) n z.1,cubePiIter (2*(n+1)) n z.2)
    rw [axis_inverse_forward]
    apply Prod.ext
    · change inverse n (cubePiIter 2 n (forward n z.1)) = cubePiIter (2*(n+1)) n z.1
      rw [inverse_piIter,ih,← cubePiIter_add]
      have h : 2+2*n = 2*(n+1) := by omega
      rw [h]
    · change inverse n (cubePiIter 2 n (forward n z.2)) = cubePiIter (2*(n+1)) n z.2
      rw [inverse_piIter,ih,← cubePiIter_add]
      have h : 2+2*n = 2*(n+1) := by omega
      rw [h]
end GaussianTensorExecution
