-- Prove2me | solution 1 for GaussianTensorExecution.inverse_forward_leaf_sameValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/dc93780c-cddf-48c3-9276-7d4314997cbd

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianTensorExecution_get_map
import Theorems.Thm_GaussianTensorExecution_inverse_forward
import Theorems.Thm_GaussianTensorExecution_shifted_tag_sameValue

set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (n e : Nat) (z : Cube n) (p : Path n) :
    SameValue ⟨get n (inverse n (forward n z)) p,e+2*n⟩ ⟨get n z p,e⟩ := by
  rw [inverse_forward]
  simp only [cubePiIter,get_map]
  exact shifted_tag_sameValue (2*n) e _
end GaussianTensorExecution
