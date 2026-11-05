-- Prove2me | solution 1 for GaussianSynthesis.corrected_scatter_sum_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:44:21.667798+00:00
-- url     : https://prove2.me/submissions/9f8cf365-bf8c-47b0-8d44-2f5881e779e3

import Definitions.Def_DyadicCertificates
import Definitions.Def_GaussianLattice
import Definitions.Def_GaussianScalarCircuits
import Theorems.Thm_GaussianSynthesis_corrected_scatter_column_exact

set_option autoImplicit true
open GaussianSynthesis
namespace GaussianSynthesis
theorem _root_.solution (xs : List (Int × Int))
    (hj : ∀ entry ∈ xs, 0 ≤ entry.2 ∧ entry.2 ≤ 3) :
    sumCorrectedScatter64 xs = 64*sumDiagonalSources xs := by
  induction xs with
  | nil => simp [sumCorrectedScatter64, sumDiagonalSources]
  | cons entry xs ih =>
    have hfirst := hj entry (by simp)
    have hrest : ∀ e ∈ xs, 0 ≤ e.2 ∧ e.2 ≤ 3 := by
      intro e he
      exact hj e (by simp [he])
    simp only [sumCorrectedScatter64, sumDiagonalSources]
    rw [corrected_scatter_column_exact _ _ hfirst, ih hrest]
    grind
end GaussianSynthesis
