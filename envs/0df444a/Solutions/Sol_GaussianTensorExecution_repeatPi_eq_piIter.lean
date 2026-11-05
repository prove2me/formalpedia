-- Prove2me | solution 1 for GaussianTensorExecution.repeatPi_eq_piIter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/bab4f84b-a58a-426e-af4a-62c3b79175d9

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution

set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (k : Nat) (z : GInt) : repeatPi k z = piIter k z := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [repeatPi,piIter,ih]
end GaussianTensorExecution
