-- Prove2me | solution 1 for CompactnessConjecture.proposedFamilyFree_minDegree_ambient_sixteenth_power_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:02.568649+00:00
-- url     : https://prove2.me/submissions/76efcf77-7388-468d-817e-af534225e2f9

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_CompactnessConjecture_fourPathHeavyThreshold_low_degree_fourth_le
import Theorems.Thm_CompactnessConjecture_proposedFamilyFree_minDegree_sixteenth_power_le

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open Filter Finset SimpleGraph
open scoped Classical Topology
namespace CompactnessConjecture
theorem _root_.solution
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
end CompactnessConjecture
