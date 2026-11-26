-- Prove2me | solution 1 for CollatzEndpointTransport.FixedTotal.actualLevelBadMass_cast_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:39:57.620436+00:00
-- url     : https://prove2.me/submissions/3f4d6222-ca83-4c55-8d4a-accf23e271f0

import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalLevelBadMass
import Definitions.Def_CollatzEndpointTransport_Linear_OptimizedLinearPullbackConstants
import Definitions.Def_CollatzEndpointTransport_Linear_FixedTotalNonlinearShell
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_three_pow_rpow_one_sub_div
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_levelCriticalFactor_eq
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_actualLevelBadMass_cast_le_raw
import Theorems.Thm_CollatzEndpointTransport_FixedTotal_card_actualLevelBadEndpointSet_le


set_option autoImplicit false
open CollatzEndpointTransport
open CollatzEndpointTransport.FixedTotal
open Nat Finset
noncomputable section
namespace CollatzEndpointTransport.FixedTotal
theorem _root_.solution
    {S : Set ℕ} {C D : ℝ}
    (hS : QuantitativeDensity.IsCDDense S C D)
    (M s : ℕ) (E : ℝ)
    (hE : 0 < E) (hs : s ≤ M) :
    (actualLevelBadMass S M s : ℝ) ≤
      C * E ^ 2 * (sourceOddLevel M s).card *
          (Real.exp (-D * Real.log 3)) ^ (s + 1) +
        E⁻¹ * Real.sqrt 3 *
          actualLevelCriticalContribution M s := by
  have hraw :=
    actualLevelBadMass_cast_le_raw S M s E hE hs
  have hcard :=
    card_actualLevelBadEndpointSet_le hS M s
  calc
    (actualLevelBadMass S M s : ℝ) ≤
      E ^ 2 *
          ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (actualLevelBadEndpointSet S M s).card +
        E⁻¹ * Real.sqrt
            ((3 : ℝ) ^ (s + 1) /
              (sourceOddLevel M s).card) *
          (∑ y ∈ actualLevelEndpointSet M s,
            (actualLevelFiberCard M s y : ℝ) *
              Real.sqrt (actualLevelFiberCard M s y)) := hraw
    _ ≤
      E ^ 2 *
          ((sourceOddLevel M s).card : ℝ) /
          (3 : ℝ) ^ (s + 1) *
          (C * ((3 : ℝ) ^ (s + 1)) ^ (1 - D)) +
        E⁻¹ * Real.sqrt
            ((3 : ℝ) ^ (s + 1) /
              (sourceOddLevel M s).card) *
          (∑ y ∈ actualLevelEndpointSet M s,
            (actualLevelFiberCard M s y : ℝ) *
              Real.sqrt (actualLevelFiberCard M s y)) := by
        gcongr
    _ =
      C * E ^ 2 * (sourceOddLevel M s).card *
          (Real.exp (-D * Real.log 3)) ^ (s + 1) +
        E⁻¹ * Real.sqrt 3 *
          actualLevelCriticalContribution M s := by
        rw [show
          E⁻¹ * Real.sqrt
                ((3 : ℝ) ^ (s + 1) /
                  (sourceOddLevel M s).card) *
              (∑ y ∈ actualLevelEndpointSet M s,
                (actualLevelFiberCard M s y : ℝ) *
                  Real.sqrt (actualLevelFiberCard M s y)) =
            E⁻¹ *
              (Real.sqrt
                  ((3 : ℝ) ^ (s + 1) /
                    (sourceOddLevel M s).card) *
                (∑ y ∈ actualLevelEndpointSet M s,
                  (actualLevelFiberCard M s y : ℝ) *
                    Real.sqrt (actualLevelFiberCard M s y))) by ring]
        rw [levelCriticalFactor_eq M s hs]
        rw [show
          E ^ 2 * ((sourceOddLevel M s).card : ℝ) /
                (3 : ℝ) ^ (s + 1) *
                (C * ((3 : ℝ) ^ (s + 1)) ^ (1 - D)) =
            C * E ^ 2 * (sourceOddLevel M s).card *
              (((3 : ℝ) ^ (s + 1)) ^ (1 - D) /
                (3 : ℝ) ^ (s + 1)) by ring]
        rw [three_pow_rpow_one_sub_div]
        ring
end CollatzEndpointTransport.FixedTotal
