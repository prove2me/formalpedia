-- Prove2me | solution 1 for GaussianTensorExecution.forward_impulse_first
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/741e9c06-8f43-4cc6-952b-81ea5d6332ab

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_cubeI_zero
import Theorems.Thm_GaussianTensorExecution_cubeAdd_zero_left
import Theorems.Thm_GaussianTensorExecution_forward_zero

set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n : Nat) :
    get n (forward n (lastImpulse n)) (firstPath n) = ⟨1,0⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [forward,lastImpulse,firstPath,get,Bool.false_eq_true,↓reduceIte]
    simp only [axisForward]
    rw [forward_zero,cubeI_zero,cubeAdd_zero_left]
    exact ih
end GaussianTensorExecution
