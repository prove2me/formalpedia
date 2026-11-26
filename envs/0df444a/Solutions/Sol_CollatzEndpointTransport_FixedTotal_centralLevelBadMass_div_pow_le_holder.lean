-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.centralLevelBadMass_div_pow_le_holder
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:51:48.569194+00:00
-- url     : https://prove2.me/submissions/8688e563-8b0b-405f-a569-2652a0245005

import Definitions.Def_CollatzEndpointTransport_Linear_SharpCentralRenyiPullback
import Mathlib.Analysis.MeanInequalities
import Definitions.Def_CollatzEndpointTransport_Linear_RefinedCentralRenyiTransport
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelBadMass_cast_le_holder_raw
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelBadEndpointDensity_le
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_holder_product_normalization
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_sourceOddLevel
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_centralLevelRenyiFactor_eq


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
open scoped Real
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M s : ℕ) (theta eta : ℝ)
    (htheta : 0 < theta) (hs : s ≤ M) :
    (centralLevelBadMass S M s theta eta : ℝ) / (2 : ℝ) ^ M ≤
      (((sourceOddLevel M s).card : ℝ) / (2 : ℝ) ^ M) *
        (C * (Real.exp (-D * Real.log 3)) ^ (s + 1)) ^
          (theta / (1 + theta)) *
        (centralLevelRenyiInformation M s theta eta /
          (sourceOddLevel M s).card) ^ (1 / (1 + theta)) := by
  have hNnat : 0 < (sourceOddLevel M s).card := by
    rw [card_sourceOddLevel]
    exact Nat.choose_pos hs
  have hN : 0 < ((sourceOddLevel M s).card : ℝ) := by exact_mod_cast hNnat
  have hR : 0 < (3 : ℝ) ^ (s + 1) := by positivity
  have hP : 0 < (2 : ℝ) ^ M := by positivity
  have hraw := centralLevelBadMass_cast_le_holder_raw
    S M s theta eta htheta
  have hnormalize := holder_product_normalization
    (E := ((centralLevelBadEndpointSet S M s theta eta).card : ℝ))
    (moment := ∑ y ∈ centralLevelEndpointSet M s theta eta,
      (centralLevelFiberCard M s theta eta y : ℝ) ^ (1 + theta))
    (info := centralLevelRenyiInformation M s theta eta)
    (N := ((sourceOddLevel M s).card : ℝ))
    (R := (3 : ℝ) ^ (s + 1)) (P := (2 : ℝ) ^ M)
    hN hR hP (Nat.cast_nonneg _)
    (sum_nonneg fun _ _ => by positivity)
    (centralLevelRenyiFactor_eq M s theta eta).symm htheta
  have hdensity := centralLevelBadEndpointDensity_le hS M s theta eta
  have hrho : 0 ≤ theta / (1 + theta) := by positivity
  have hinfoNonneg :
      0 ≤ centralLevelRenyiInformation M s theta eta := by
    unfold centralLevelRenyiInformation
    positivity
  calc
    (centralLevelBadMass S M s theta eta : ℝ) / (2 : ℝ) ^ M ≤
        (((centralLevelBadEndpointSet S M s theta eta).card : ℝ) ^
            (theta / (1 + theta)) *
          (∑ y ∈ centralLevelEndpointSet M s theta eta,
            (centralLevelFiberCard M s theta eta y : ℝ) ^ (1 + theta)) ^
              (1 / (1 + theta))) / (2 : ℝ) ^ M :=
      div_le_div_of_nonneg_right hraw hP.le
    _ = (((sourceOddLevel M s).card : ℝ) / (2 : ℝ) ^ M) *
          (((centralLevelBadEndpointSet S M s theta eta).card : ℝ) /
            (3 : ℝ) ^ (s + 1)) ^ (theta / (1 + theta)) *
          (centralLevelRenyiInformation M s theta eta /
            (sourceOddLevel M s).card) ^ (1 / (1 + theta)) := hnormalize
    _ ≤ (((sourceOddLevel M s).card : ℝ) / (2 : ℝ) ^ M) *
          (C * (Real.exp (-D * Real.log 3)) ^ (s + 1)) ^
            (theta / (1 + theta)) *
          (centralLevelRenyiInformation M s theta eta /
            (sourceOddLevel M s).card) ^ (1 / (1 + theta)) := by
      apply mul_le_mul_of_nonneg_right _
        (Real.rpow_nonneg (div_nonneg hinfoNonneg hN.le) _)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (by positivity) hdensity hrho
end CollatzEndpointTransport.FixedTotal
