-- Prove2me | solution 1 for Erdos180.proposedFamilyFree_minDegree_ambient_sixteenth_power_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:19:19.252188+00:00
-- url     : https://prove2.me/submissions/ba4f6ea0-29e4-4400-af1c-f8c90c36a4fd

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Theorems.Thm_Erdos180_proposedFamilyFree_minDegree_sixteenth_power_le

namespace Erdos180

noncomputable section
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma fourPathHeavyThreshold_low_degree_fourth_le
    (N d : ℕ)
    (hN : 0 < N)
    (hd : 2 ≤ d)
    (hlow : ¬ (3 : ℝ) ≤
      fourPathHeavyThreshold N (d * (d - 1) ^ 3)) :
    (d : ℝ) ^ 4 ≤ 48 * (N : ℝ) := by
  have hNReal : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hthreshold :
      fourPathHeavyThreshold N (d * (d - 1) ^ 3) < 3 :=
    lt_of_not_ge hlow
  have hp :
      ((d * (d - 1) ^ 3 : ℕ) : ℝ) < 6 * (N : ℝ) := by
    unfold fourPathHeavyThreshold at hthreshold
    have hden : 0 < 2 * (N : ℝ) := by positivity
    have hclear := (div_lt_iff₀ hden).mp hthreshold
    nlinarith
  have hpredNat : d ≤ 2 * (d - 1) := by omega
  have hpredReal : (d : ℝ) ≤ 2 * ((d - 1 : ℕ) : ℝ) := by
    exact_mod_cast hpredNat
  have hpowers :
      (d : ℝ) ^ 3 ≤ (2 * ((d - 1 : ℕ) : ℝ)) ^ 3 := by
    gcongr
  have hfourth :
      (d : ℝ) ^ 4 ≤
        8 * ((d * (d - 1) ^ 3 : ℕ) : ℝ) := by
    calc
      (d : ℝ) ^ 4 = (d : ℝ) * (d : ℝ) ^ 3 := by ring
      _ ≤ (d : ℝ) *
          (2 * ((d - 1 : ℕ) : ℝ)) ^ 3 :=
        mul_le_mul_of_nonneg_left hpowers (Nat.cast_nonneg d)
      _ = 8 * ((d * (d - 1) ^ 3 : ℕ) : ℝ) := by
        push_cast
        ring
  nlinarith

end

end Erdos180

open Erdos180
open Filter Finset SimpleGraph
open scoped Classical Topology

theorem solution
    {N n : ℕ} (host : SimpleGraph (Fin N))
    (hN : 0 < N) (hn : 0 < n) (hNn : N ≤ n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin N, d ≤ host.degree v) :
    (d : ℝ) ^ 16 ≤
      compactnessDegreePowerConstant * (n : ℝ) ^ 5 := by
  classical
  have hNreal : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hNn
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hcoefLow :
      (48 : ℝ) ^ (4 : ℕ) ≤ compactnessDegreePowerConstant := by
    norm_num [compactnessDegreePowerConstant]
  have hcoefHigh :
      (1769472 : ℝ) ≤ compactnessDegreePowerConstant := by
    norm_num [compactnessDegreePowerConstant]
  have hcoefOne : (1 : ℝ) ≤ compactnessDegreePowerConstant := by
    norm_num [compactnessDegreePowerConstant]
  by_cases hd : 2 ≤ d
  · by_cases hthreshold : (3 : ℝ) ≤
      fourPathHeavyThreshold N (d * (d - 1) ^ 3)
    · have hhigh := proposedFamilyFree_minDegree_sixteenth_power_le
        host hN hfree hbip d hd hdegree hthreshold
      calc
        (d : ℝ) ^ 16 ≤ 1769472 * (N : ℝ) ^ 5 := hhigh
        _ ≤ 1769472 * (n : ℝ) ^ 5 := by
          gcongr
        _ ≤ compactnessDegreePowerConstant * (n : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_right hcoefHigh (by positivity)
    · have hlow := fourPathHeavyThreshold_low_degree_fourth_le
        N d hN hd hthreshold
      have hfour :
          (N : ℝ) ^ 4 ≤ (n : ℝ) ^ 5 := by
        calc
          (N : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 := by gcongr
          _ = (n : ℝ) ^ 4 * 1 := by ring
          _ ≤ (n : ℝ) ^ 4 * (n : ℝ) :=
            mul_le_mul_of_nonneg_left hnreal (by positivity)
          _ = (n : ℝ) ^ 5 := by ring
      calc
        (d : ℝ) ^ 16 = ((d : ℝ) ^ 4) ^ 4 := by ring
        _ ≤ (48 * (N : ℝ)) ^ 4 := by gcongr
        _ = (48 : ℝ) ^ 4 * (N : ℝ) ^ 4 := by ring
        _ ≤ (48 : ℝ) ^ 4 * (n : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_left hfour (by positivity)
        _ ≤ compactnessDegreePowerConstant * (n : ℝ) ^ 5 :=
          mul_le_mul_of_nonneg_right hcoefLow (by positivity)
  · have hdNat : d ≤ 1 := by omega
    have hdReal : (d : ℝ) ≤ 1 := by exact_mod_cast hdNat
    calc
      (d : ℝ) ^ 16 ≤ (1 : ℝ) ^ 16 := by gcongr
      _ = 1 ^ (5 : ℕ) := by norm_num
      _ ≤ (n : ℝ) ^ 5 := by gcongr
      _ = 1 * (n : ℝ) ^ 5 := by ring
      _ ≤ compactnessDegreePowerConstant * (n : ℝ) ^ 5 :=
        mul_le_mul_of_nonneg_right hcoefOne (by positivity)
