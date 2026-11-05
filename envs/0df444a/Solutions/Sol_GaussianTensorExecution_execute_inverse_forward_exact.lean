-- Prove2me | solution 1 for GaussianTensorExecution.execute_inverse_forward_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/20d5fd47-6463-4b59-8c6d-7f4d7632955c

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_inverse_forward_leaf_sameValue

set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n : Nat) (x : TaggedCube n) (p : Path n) :
    SameValue (coordinate n (executeInverse n (executeForward n x)) p)
      (coordinate n x p) := by
  unfold coordinate executeInverse executeForward
  simp only
  have he : x.exponent+n+n = x.exponent+2*n := by omega
  rw [he]
  exact inverse_forward_leaf_sameValue n x.exponent x.numerators p
end GaussianTensorExecution
