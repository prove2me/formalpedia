-- Prove2me | solution 1 for GaussianTensorExecution.cubeMap_congr
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/97f13148-f24e-4873-a383-ff026aed73b8

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n : Nat) (f g : GInt → GInt) (h : ∀ z, f z = g z)
    (z : Cube n) : cubeMap f n z = cubeMap g n z := by
  induction n with
  | zero => exact h z
  | succ n ih =>
    apply Prod.ext
    · exact ih z.1
    · exact ih z.2
end GaussianTensorExecution
