-- Prove2me | solution 1 for GaussianTensorExecution.inverse_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/fd770023-0eb0-4189-985a-53f685cae2a6

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_axisInverse_pi
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n : Nat) (z : Cube n) :
    inverse n (cubePi n z) = cubePi n (inverse n z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Cube n × Cube n at z
    change
      (inverse n (axisInverse n (cubePi n z.1,cubePi n z.2)).1,
       inverse n (axisInverse n (cubePi n z.1,cubePi n z.2)).2) =
      (cubePi n (inverse n (axisInverse n z).1),
       cubePi n (inverse n (axisInverse n z).2))
    rw [axisInverse_pi]
    apply Prod.ext
    · exact ih _
    · exact ih _
end GaussianTensorExecution
