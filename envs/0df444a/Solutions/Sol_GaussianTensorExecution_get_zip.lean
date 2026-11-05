-- Prove2me | solution 1 for GaussianTensorExecution.get_zip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/fcdc7102-9ccb-4c5a-9fc4-d61908e52d94

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution

set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n : Nat) (f : GInt → GInt → GInt)
    (u v : Cube n) (p : Path n) :
    get n (cubeZip f n u v) p = f (get n u p) (get n v p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨b,p⟩
    cases b <;> simp only [get,cubeZip,Bool.false_eq_true,↓reduceIte]
    · exact ih _ _ p
    · exact ih _ _ p
end GaussianTensorExecution
