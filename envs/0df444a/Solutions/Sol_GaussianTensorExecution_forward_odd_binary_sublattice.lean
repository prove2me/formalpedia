-- Prove2me | solution 1 for GaussianTensorExecution.forward_odd_binary_sublattice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/d81109ba-fba7-4a47-b68c-f1cc96d73cf5

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_repeatPi_eq_piIter
import Theorems.Thm_GaussianParity_odd_binary_conversion
import Theorems.Thm_GaussianParity_odd_binary_numerator_parity


set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (p q : Nat) (z : Cube (2*q+1))
    (path : Path (2*q+1)) :
    ∃ w : GInt, piIter (2*p+(2*q+1)) w =
      scale ((2 : Int)^(p+q+1)) (get (2*q+1) (forward (2*q+1) z) path) ∧ PiDvd w := by
  let a := get (2*q+1) (forward (2*q+1) z) path
  refine ⟨repeatNegI (p+q+1) (mulPi a),?_,odd_binary_numerator_parity (p+q) a⟩
  have hc := odd_binary_conversion (p+q) a
  have he : 2*p+(2*q+1) = 2*(p+q)+1 := by omega
  rw [he]
  simpa only [repeatPi_eq_piIter] using hc
end GaussianTensorExecution
