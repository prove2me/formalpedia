-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_centralRenyi_startup_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:28.603951+00:00
-- url     : https://prove2.me/submissions/21662337-8c1f-4960-a1fe-8d6aae883cd6

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_sourceEndpointBad_div_pow_le_centralRenyi_sharp
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyiAlpha_lt_log_ratio
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralRenyi_startup


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {S : Set ℕ} {C D theta eta : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (heta0 : 0 < eta)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (M : ℕ) (hM : centralRenyiStartupScale theta eta ≤ M) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      ((((M + 1) *
          2 ^ (M - centralRenyiDiscardDepth eta M) : ℕ) : ℝ) /
          (2 ^ M : ℝ)) +
        2 * Real.exp (-2 * (eta / 4) ^ 2 * M) +
        (C * Real.exp (-D * Real.log 3) +
            2 * (3 : ℝ) ^ theta * centralMomentConstant theta eta *
              (M + 1 : ℝ) ^ (1 + theta)) *
          Real.exp (-centralRenyiRate theta D * M) := by
  have hetaHalf : eta ≤ 1 / 2 := by
    have ha := centralRenyiAlpha_lt_log_ratio htheta0
    have hlog : Real.log 2 / Real.log 3 < 1 := by
      rw [div_lt_one (Real.log_pos (by norm_num))]
      exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
    linarith
  obtain ⟨hKM, hK, hetaM, hstartup⟩ :=
    centralRenyi_startup htheta0 heta0 heta1 hM
  exact sourceEndpointBad_div_pow_le_centralRenyi_sharp
    hS htheta0 htheta1 heta0 hetaHalf heta1
    M (centralRenyiDiscardDepth eta M) hKM hK hetaM hstartup
end CollatzEndpointTransport.FixedTotal
