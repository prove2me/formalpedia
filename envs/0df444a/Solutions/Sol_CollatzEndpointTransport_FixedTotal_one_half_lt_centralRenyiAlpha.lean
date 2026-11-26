-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.one_half_lt_centralRenyiAlpha
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:38:24.994705+00:00
-- url     : https://prove2.me/submissions/84db592f-8fff-4449-9d22-b4d0ed1f56a0

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalCriticalMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Slope
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.List.DropRight
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAlpha_den_pos

set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta : ℝ} (htheta0 : 0 < theta) (htheta1 : theta < 1) :
    (1 / 2 : ℝ) < centralRenyiAlpha theta := by
  have hconc :=
    (Real.strictConcaveOn_rpow htheta0 htheta1).2
      (show (1 : ℝ) ∈ Set.Ici 0 by norm_num)
      (show (3 : ℝ) ∈ Set.Ici 0 by norm_num)
      (by norm_num : (1 : ℝ) ≠ 3)
      (show 0 < (1 / 2 : ℝ) by norm_num)
      (show 0 < (1 / 2 : ℝ) by norm_num)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have hconc' :
      (1 / 2 : ℝ) * (1 : ℝ) ^ theta +
          (1 / 2 : ℝ) * (3 : ℝ) ^ theta <
        (2 : ℝ) ^ theta := by
    norm_num [smul_eq_mul] at hconc ⊢
    nlinarith
  rw [Real.one_rpow] at hconc'
  unfold centralRenyiAlpha
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)
    (centralRenyiAlpha_den_pos htheta0)]
  linarith
end CollatzEndpointTransport.FixedTotal
