-- Prove2me | solution 1 for GaussianTensorExecution.cubeMap_zip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/1bf2ea34-50e6-4173-84bc-87bdd13169ec

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n : Nat) (f : GInt → GInt)
    (g : GInt → GInt → GInt) (h : ∀ u v, f (g u v) = g (f u) (f v))
    (u v : Cube n) :
    cubeMap f n (cubeZip g n u v) =
      cubeZip g n (cubeMap f n u) (cubeMap f n v) := by
  induction n with
  | zero => exact h u v
  | succ n ih =>
    apply Prod.ext
    · exact ih u.1 v.1
    · exact ih u.2 v.2
end GaussianTensorExecution
