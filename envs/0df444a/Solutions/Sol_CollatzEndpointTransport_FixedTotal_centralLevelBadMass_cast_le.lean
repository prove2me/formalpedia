-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralLevelBadMass_cast_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:45:14.631799+00:00
-- url     : https://prove2.me/submissions/10b36641-388d-42f3-a469-b64ba5b1456e

import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiShell
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Definitions.Def_CollatzEndpointTransport_Linear_CentralRenyiPullback
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_centralLevelBadEndpointSet_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelBadMass_cast_le_raw
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelRenyiFactor_eq
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_three_pow_rpow_one_sub_div


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real Topology
noncomputable section
attribute [local instance] CollatzEndpointTransport.FixedTotal.centralPullbackSourceCodeDecidableEq
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M s : ℕ) (theta eta Q : ℝ)
    (hQ : 0 < Q) (htheta : 0 < theta) (hs : s ≤ M) :
    (centralLevelBadMass S M s theta eta : ℝ) ≤
      C * Q * (sourceOddLevel M s).card *
          (Real.exp (-D * Real.log 3)) ^ (s + 1) +
        Q ^ (-theta) * centralLevelRenyiInformation M s theta eta := by
  have hraw := centralLevelBadMass_cast_le_raw
    S M s theta eta Q hQ htheta hs
  have hcard := card_centralLevelBadEndpointSet_le hS M s theta eta
  calc
    (centralLevelBadMass S M s theta eta : ℝ) ≤
      Q * ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (centralLevelBadEndpointSet S M s theta eta).card +
        Q ^ (-theta) *
          (((3 : ℝ) ^ (s + 1)) /
            (sourceOddLevel M s).card) ^ theta *
          (∑ y ∈ centralLevelEndpointSet M s theta eta,
            (centralLevelFiberCard M s theta eta y : ℝ) ^
              (1 + theta)) := hraw
    _ ≤ Q * ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (C * ((3 : ℝ) ^ (s + 1)) ^ (1 - D)) +
        Q ^ (-theta) *
          (((3 : ℝ) ^ (s + 1)) /
            (sourceOddLevel M s).card) ^ theta *
          (∑ y ∈ centralLevelEndpointSet M s theta eta,
            (centralLevelFiberCard M s theta eta y : ℝ) ^
              (1 + theta)) := by
        gcongr
    _ = C * Q * (sourceOddLevel M s).card *
          (Real.exp (-D * Real.log 3)) ^ (s + 1) +
        Q ^ (-theta) * centralLevelRenyiInformation M s theta eta := by
      rw [show
        Q ^ (-theta) *
              (((3 : ℝ) ^ (s + 1)) /
                (sourceOddLevel M s).card) ^ theta *
              (∑ y ∈ centralLevelEndpointSet M s theta eta,
                (centralLevelFiberCard M s theta eta y : ℝ) ^
                  (1 + theta)) =
            Q ^ (-theta) *
              (((((3 : ℝ) ^ (s + 1)) /
                (sourceOddLevel M s).card) ^ theta) *
              (∑ y ∈ centralLevelEndpointSet M s theta eta,
                (centralLevelFiberCard M s theta eta y : ℝ) ^
                  (1 + theta))) by ring]
      rw [centralLevelRenyiFactor_eq]
      rw [show
        Q * ((sourceOddLevel M s).card : ℝ) /
              (3 : ℝ) ^ (s + 1) *
              (C * ((3 : ℝ) ^ (s + 1)) ^ (1 - D)) =
            C * Q * (sourceOddLevel M s).card *
              ((((3 : ℝ) ^ (s + 1)) ^ (1 - D)) /
                (3 : ℝ) ^ (s + 1)) by ring]
      rw [three_pow_rpow_one_sub_div]
end CollatzEndpointTransport.FixedTotal
