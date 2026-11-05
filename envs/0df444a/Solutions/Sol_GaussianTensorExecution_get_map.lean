-- Prove2me | solution 1 for GaussianTensorExecution.get_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/c6cb44e3-9046-4edd-a1c0-70b1d70f184f

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution

set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n : Nat) (f : GInt → GInt) (z : Cube n) (p : Path n) :
    get n (cubeMap f n z) p = f (get n z p) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases p with ⟨b,p⟩
    cases b <;> simp only [get,cubeMap,Bool.false_eq_true,↓reduceIte]
    · exact ih _ p
    · exact ih _ p
end GaussianTensorExecution
