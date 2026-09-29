-- Prove2me | solution 1 for BlockCycleRotation.relation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:58:54.573891+00:00
-- url     : https://prove2.me/submissions/46700068-8aad-4bc4-af72-e555f3859db6

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Average
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_cost_add_gcd
import Theorems.Thm_BlockCycleRotation_psi_rat
import Mathlib

open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

/-- Shifting the first argument by the second does not change the gcd. -/
theorem gcd_add_left (k r : ℕ) : Nat.gcd (k + r) r = Nat.gcd k r := by
  rw [Nat.gcd_comm (k + r) r, Nat.gcd_comm k r]
  exact Nat.gcd_add_self_right r k

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem min_self_sub {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    min ((k : ℝ) / (n : ℝ)) (1 - (k : ℝ) / (n : ℝ))
      = ((min k (n - k) : ℕ) : ℝ) / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsub : 1 - (k : ℝ) / (n : ℝ) = ((n - k : ℕ) : ℝ) / (n : ℝ) := by
    have hc : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
      have := Nat.cast_sub (R := ℝ) hk
      linarith [this]
    rw [hc]
    field_simp
  rw [hsub]
  rcases le_total k (n - k) with h | h
  · have hd : ((k : ℕ) : ℝ) / (n : ℝ) ≤ ((n - k : ℕ) : ℝ) / (n : ℝ) := by
      gcongr
    rw [min_eq_left hd, Nat.min_eq_left h]
  · have hd : ((n - k : ℕ) : ℝ) / (n : ℝ) ≤ ((k : ℕ) : ℝ) / (n : ℝ) := by
      gcongr
    rw [min_eq_right hd, Nat.min_eq_right h]

theorem gcd_min_self_sub {n k : ℕ} (hk : k ≤ n) :
    Nat.gcd n (min k (n - k)) = Nat.gcd n k := by
  rcases le_total k (n - k) with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h]
    calc Nat.gcd n (n - k) = Nat.gcd (k + (n - k)) (n - k) := by congr 1; omega
      _ = Nat.gcd k (n - k) := gcd_add_left k (n - k)
      _ = Nat.gcd (n - k) k := Nat.gcd_comm _ _
      _ = Nat.gcd ((n - k) + k) k := (gcd_add_left (n - k) k).symm
      _ = Nat.gcd n k := by congr 1; omega

end BlockCycleRotation

open BlockCycleRotation in
/-- **Equation (relation).**  `M(n,k) = n·f(k/n) - gcd(n,k)`. -/
theorem solution {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    ((algCost n k : ℕ) : ℝ) + ((Nat.gcd n k : ℕ) : ℝ)
      = (n : ℝ) * fCost ((k : ℝ) / (n : ℝ)):= by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set j := min k (n - k) with hj
  have hj2 : 2 * j ≤ n := by omega
  have hcost : cost n j + Nat.gcd n j = n + 2 * remSum n j := cost_add_gcd j n
  have hcostR : ((cost n j : ℕ) : ℝ) + ((Nat.gcd n j : ℕ) : ℝ)
      = (n : ℝ) + 2 * ((remSum n j : ℕ) : ℝ) := by exact_mod_cast hcost
  have hpsi : (n : ℝ) * psi ((j : ℝ) / (n : ℝ)) = 2 * (remSum n j : ℝ) := psi_rat j n hn hj2
  rw [fCost, min_self_sub hn hk, ← hj]
  have halg : algCost n k = cost n j := rfl
  have hgcd : Nat.gcd n j = Nat.gcd n k := gcd_min_self_sub hk
  rw [halg, ← hgcd]
  rw [mul_add, mul_one, hpsi]
  linarith [hcostR]
