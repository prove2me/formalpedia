-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.sourceEndpointBad_div_pow_le_centralRenyi_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:59:33.247385+00:00
-- url     : https://prove2.me/submissions/f3c5fe06-1c7d-457a-b2e8-0cb29e05db94

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralSourceEndpointBad_div_pow_le_balanced_sharp
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_centralDiscardedSourceSet_cast_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceEndpointBad_le_discard_add_central


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
    (heta0 : 0 < eta) (hetaHalf : eta ≤ 1 / 2)
    (heta1 : eta < centralRenyiAlpha theta - 1 / 2)
    (M K : ℕ) (hKM : K ≤ M)
    (hK : (K : ℝ) ≤ eta * M / 8)
    (hetaM : 4 ≤ eta * M)
    (hstartup : ∀ N : ℕ, M - K ≤ N → N ≤ M →
      1 < N ∧
      (1 / 2 - eta) * N > 1 / 2 ∧
      2 * eta ≤ centralRenyiGap theta eta * ((N : ℝ) - 1) ∧
      (1 / 2 : ℝ) ≤
        (Real.log 2 / Real.log 3 - (1 / 2 + eta)) * N) :
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
      (((M + 1) * 2 ^ (M - K) : ℕ) : ℝ) / (2 ^ M : ℝ) +
        2 * Real.exp (-2 * (eta / 4) ^ 2 * M) +
        (C * Real.exp (-D * Real.log 3) +
            2 * (3 : ℝ) ^ theta * centralMomentConstant theta eta *
              (M + 1 : ℝ) ^ (1 + theta)) *
          Real.exp (-centralRenyiRate theta D * M) := by
  have hsplit := card_sourceEndpointBad_le_discard_add_central S M theta eta
  have hdiscard := card_centralDiscardedSourceSet_cast_le
    hKM heta0 hetaHalf hK hetaM hstartup
  have hcentral := centralSourceEndpointBad_div_pow_le_balanced_sharp
    hS htheta0 htheta1 heta0 heta1 M
  have hpow : 0 < (2 : ℝ) ^ M := by positivity
  have hsplitR :
      ((sourceEndpointBad S M).card : ℝ) ≤
        (centralDiscardedSourceSet M theta eta).card +
          (centralSourceEndpointBad S M theta eta).card := by
    exact_mod_cast hsplit
  calc
    ((sourceEndpointBad S M).card : ℝ) / (2 ^ M : ℝ) ≤
        (((centralDiscardedSourceSet M theta eta).card : ℝ) +
          ((centralSourceEndpointBad S M theta eta).card : ℝ)) /
            (2 ^ M : ℝ) :=
      div_le_div_of_nonneg_right hsplitR hpow.le
    _ = ((centralDiscardedSourceSet M theta eta).card : ℝ) / (2 ^ M : ℝ) +
        ((centralSourceEndpointBad S M theta eta).card : ℝ) / (2 ^ M : ℝ) := by ring
    _ ≤ ((((M + 1) * 2 ^ (M - K) : ℕ) : ℝ) +
          (2 : ℝ) ^ M * (2 * Real.exp (-2 * (eta / 4) ^ 2 * M))) /
          (2 ^ M : ℝ) +
        (C * Real.exp (-D * Real.log 3) +
            2 * (3 : ℝ) ^ theta * centralMomentConstant theta eta *
              (M + 1 : ℝ) ^ (1 + theta)) *
          Real.exp (-centralRenyiRate theta D * M) := by
      gcongr
    _ = _ := by field_simp [hpow.ne']
end CollatzEndpointTransport.FixedTotal
