-- Prove2me | solution 1 for AvramDividend.Classical.cstar_attained_of_continuous_deriv_strict_boundary_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T15:55:24.621984+00:00
-- url     : https://prove2.me/submissions/b47b6e0e-7409-4a59-98c4-60c6b598ac56

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstarSet_closed_of_strict_boundary_gap
import Theorems.Thm_AvramDividend_Classical_cstar_attained_of_compact_initial_minimizers

open AvramDividend.Classical

theorem solution (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Set.Ici (0 : ℝ)))
    (a : ℝ) (ha : a ∈ cstarSet W)
    (hgap : deriv W a < deriv W 0) :
    (cstar W).toReal ∈ cstarSet W := by
  have hclosed : IsClosed (cstarSet W) :=
    cstarSet_closed_of_strict_boundary_gap W hcont a ha hgap
  have hcompact : IsCompact (cstarSet W ∩ Set.Icc 0 a) :=
    isCompact_Icc.of_isClosed_subset
      (hclosed.inter isClosed_Icc) Set.inter_subset_right
  exact cstar_attained_of_compact_initial_minimizers W a ha hcompact
