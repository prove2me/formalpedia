-- Prove2me | solution 1 for GaussianSynthesis.corrected_scatter_sum_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/ca828bef-2a2d-4bb7-a11a-dc94e34f85d9

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_corrected_scatter_sum_exact

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution (xs : List (Int × Int))
    (hj : ∀ entry ∈ xs, 0 ≤ entry.2 ∧ entry.2 ≤ 3) :
    sumCorrectedScatter64 xs / 64 = sumDiagonalSources xs := by
  rw [corrected_scatter_sum_exact xs hj]
  omega
end GaussianSynthesis
