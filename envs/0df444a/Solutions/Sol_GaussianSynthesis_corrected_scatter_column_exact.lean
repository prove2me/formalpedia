-- Prove2me | solution 1 for GaussianSynthesis.corrected_scatter_column_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/3c9ab008-c2d2-4e63-97f2-5e7e3184abdb

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_corrected_bulk_coefficient

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution (x j : Int) (hj : 0 ≤ j ∧ j ≤ 3) :
    correctedScatterColumn64 x j = 64*(if j=3 then x else 0) := by
  unfold correctedScatterColumn64
  have hc := corrected_bulk_coefficient j hj
  unfold correctedBulkCoefficientNumerator at hc
  split <;> split <;> split <;> grind
end GaussianSynthesis
