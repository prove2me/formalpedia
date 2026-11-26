-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.tsum_terminal_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:46:59.277626+00:00
-- url     : https://prove2.me/submissions/d1cd283a-0747-431b-bf40-65ab7d649a09

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiCore
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiReverse
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_norm_centralReverseTailRatio_lt_one
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_tsum_shifted_choose_mul_geometric
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_shifted_terminal_majorant_eq
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_one_lt_two_rpow


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {theta pi : ℝ} {r : ℕ}
    (htheta : 0 < theta) (hpi0 : 0 ≤ pi) (hpi1 : pi ≤ 1)
    (hr : 0 < r) :
    ∑' n : ℕ,
        pi ^ r * (1 - pi) ^ n *
          ((n + r - 1).choose (r - 1) : ℝ) *
          realTerminalSpendTerm theta r (n + r) =
      (3 : ℝ) ^ (-theta) *
        centralRenyiRatio theta pi ^ r := by
  have hq := norm_centralReverseTailRatio_lt_one htheta hpi0 hpi1
  simp_rw [shifted_terminal_majorant_eq (theta := theta) (pi := pi) hr]
  rw [tsum_mul_left]
  rw [tsum_shifted_choose_mul_geometric r hr hq]
  unfold centralRenyiRatio centralReverseTailRatio
  have htwo : 0 < (2 : ℝ) ^ theta := by positivity
  have hden : 0 < (2 : ℝ) ^ theta - 1 + pi := by
    linarith [one_lt_two_rpow htheta]
  rw [show 1 - (1 - pi) / (2 : ℝ) ^ theta =
      ((2 : ℝ) ^ theta - 1 + pi) / (2 : ℝ) ^ theta by
        field_simp
        ring]
  simp_rw [div_pow]
  field_simp [htwo.ne', hden.ne'] <;> ring
end CollatzEndpointTransport.FixedTotal
