-- Prove2me | solution 1 for GaussianTensorExecution.forward_leaf_binary_grid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/9ce25399-59aa-409a-af0a-c2534929812d

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_repeatPi_eq_piIter
import Theorems.Thm_GaussianParity_binary_grid_conversion


set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n e : Nat) (z : Cube n) (p : Path n) :
    ∃ w : GInt, piIter (e+n) w = scale ((2 : Int)^((e+n+1)/2)) (get n (forward n z) p) := by
  rcases binary_grid_conversion (e+n) (get n (forward n z) p) with ⟨w,hw⟩
  exact ⟨w,by simpa only [repeatPi_eq_piIter] using hw⟩
end GaussianTensorExecution
