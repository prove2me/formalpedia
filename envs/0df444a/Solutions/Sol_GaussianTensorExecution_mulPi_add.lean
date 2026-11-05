-- Prove2me | solution 1 for GaussianTensorExecution.mulPi_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/8cf22b77-ca01-4980-a73c-b435dd9a6720

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (u v : GInt) : mulPi (add u v) = add (mulPi u) (mulPi v) := by
  apply GInt.ext <;> simp only [mulPi,add] <;> omega
end GaussianTensorExecution
