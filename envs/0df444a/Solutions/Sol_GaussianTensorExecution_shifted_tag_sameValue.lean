-- Prove2me | solution 1 for GaussianTensorExecution.shifted_tag_sameValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.80903+00:00
-- url     : https://prove2.me/submissions/c1b41db6-ccac-48f2-842a-cbbb41a9a3d6

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianParity_piIter_add


set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (k e : Nat) (z : GInt) :
    SameValue ⟨piIter k z,e+k⟩ ⟨z,e⟩ := by
  simp only [SameValue]
  rw [← piIter_add]
end GaussianTensorExecution
