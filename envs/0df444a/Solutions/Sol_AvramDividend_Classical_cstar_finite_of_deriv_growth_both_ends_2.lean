-- Prove2me | solution 2 for AvramDividend.Classical.cstar_finite_of_deriv_growth_both_ends
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T10:52:55.264401+00:00
-- url     : https://prove2.me/submissions/fbdcef5c-8910-4ade-b0ed-e19eb7bb3db4

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_finite_attained_of_deriv_growth_both_ends

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Filter Set
open scoped Topology ENNReal

/-- The stronger finite-and-attained result gives finiteness directly. -/
theorem solution
    (W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hcont : ContinuousOn (deriv W) (Set.Ioi 0))
    (hzero : Filter.Tendsto (deriv W) (𝓝[>] (0 : ℝ)) Filter.atTop)
    (hinfty : Filter.Tendsto (deriv W) Filter.atTop Filter.atTop) :
    cstar W < ⊤ := by
  exact (cstar_finite_attained_of_deriv_growth_both_ends
    W a ha hcont hzero hinfty).1
