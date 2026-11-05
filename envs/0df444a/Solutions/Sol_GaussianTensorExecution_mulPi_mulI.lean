-- Prove2me | solution 1 for GaussianTensorExecution.mulPi_mulI
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/7f9f9406-35fd-4c7c-bfa7-02b57cf9279c

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Definitions.Def_GaussianTensorExecution
import Theorems.Thm_GaussianParity_GInt_ext


set_option autoImplicit true
open GaussianTensorExecution
open GaussianParity GaussianSynthesis
namespace GaussianTensorExecution
theorem _root_.solution (z : GInt) : mulPi (mulI z) = mulI (mulPi z) := by
  apply GInt.ext <;> simp only [mulPi,mulI] <;> omega
end GaussianTensorExecution
