-- Prove2me | solution 1 for GaussianTensorExecution.cube_ext
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/b780d58e-1439-4b69-a21c-adabf85124dd

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n : Nat) {u v : Cube n}
    (h : ∀ p : Path n, get n u p = get n v p) : u = v := by
  induction n with
  | zero => exact h ()
  | succ n ih =>
    apply Prod.ext
    · apply ih
      intro p
      exact h (false,p)
    · apply ih
      intro p
      exact h (true,p)
end GaussianTensorExecution
