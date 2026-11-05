-- Prove2me | solution 1 for GaussianSynthesis.corrected_bulk_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/e6eb1c83-d0bc-488b-9407-cf427ef1d7f8

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution (j : Int) (hj : 0 ≤ j ∧ j ≤ 3) :
    correctedBulkCoefficientNumerator j = (if j=3 then 2 else 0) := by
  unfold correctedBulkCoefficientNumerator
  split <;> split <;> split <;> omega
end GaussianSynthesis
