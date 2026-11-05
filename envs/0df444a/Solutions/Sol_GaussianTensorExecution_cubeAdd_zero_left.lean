-- Prove2me | solution 1 for GaussianTensorExecution.cubeAdd_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/d9c63107-5244-4299-8120-724d33540629

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n : Nat) (z : Cube n) : cubeAdd n (zeroCube n) z = z := by
  induction n with
  | zero => apply GInt.ext <;> simp [cubeAdd,cubeZip,zeroCube,add]
  | succ n ih =>
    change (cubeAdd n (zeroCube n) z.1,cubeAdd n (zeroCube n) z.2) = z
    rw [ih,ih]
    cases z
    rfl
end GaussianTensorExecution
