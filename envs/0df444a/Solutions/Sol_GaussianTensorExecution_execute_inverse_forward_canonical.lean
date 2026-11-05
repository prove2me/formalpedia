-- Prove2me | solution 1 for GaussianTensorExecution.execute_inverse_forward_canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/11550b98-7b02-4140-880b-4f61f2b312d3

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_execute_inverse_forward_exact
import Theorems.Thm_GaussianSynthesis_normalize_congr


set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n : Nat) (x : TaggedCube n) (p : Path n) :
    normalize (coordinate n (executeInverse n (executeForward n x)) p) =
      normalize (coordinate n x p) :=
  normalize_congr (execute_inverse_forward_exact n x p)
end GaussianTensorExecution
