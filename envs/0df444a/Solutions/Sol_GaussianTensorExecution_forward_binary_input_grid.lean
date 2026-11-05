-- Prove2me | solution 1 for GaussianTensorExecution.forward_binary_input_grid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/d873ac60-046b-48f6-9de4-b9deac58ccee

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_forward_leaf_binary_grid

set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n p : Nat) (z : Cube n) (path : Path n) :
    ∃ w : GInt, piIter (2*p+n) w =
      scale ((2 : Int)^(p+(n+1)/2)) (get n (forward n z) path) := by
  have h := forward_leaf_binary_grid n (2*p) z path
  have he : (2*p+n+1)/2 = p+(n+1)/2 := by omega
  simpa only [he] using h
end GaussianTensorExecution
