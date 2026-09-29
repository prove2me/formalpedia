-- Prove2me | solution 1 for BlockCycleRotation.theorem10_unit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:03:19.989655+00:00
-- url     : https://prove2.me/submissions/3cf1dffd-1a7b-4e22-835b-bd6857fb0ce5

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Average
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_exists_card_divisors_le
import Theorems.Thm_BlockCycleRotation_relation
import Theorems.Thm_BlockCycleRotation_tendsto_riemann_fBar
import Theorems.Thm_BlockCycleRotation_sum_gcd_range_le
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

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

theorem fBar_eq_fCost {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1) : fBar x = fCost x := by
  unfold fBar; rw [if_pos ⟨hx0, hx⟩]

theorem tendsto_divisors_div : Tendsto (fun n : ℕ => (n.divisors.card : ℝ) / (n : ℝ))
    atTop (𝓝 0) := by
  obtain ⟨C, hC, hCd⟩ := exists_card_divisors_le (show (0 : ℝ) < 1 / 2 by norm_num)
  have hlim : Tendsto (fun n : ℕ => C / (n : ℝ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    refine Filter.Tendsto.const_div_atTop ?_ C
    exact (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  refine squeeze_zero' (Filter.Eventually.of_forall fun n => by positivity) ?_ hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 := hCd n hn.ne'
  have hpow : (n : ℝ) = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hnR]
    norm_num
  have hp : (0 : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hnR _
  rw [div_le_div_iff₀ hnR hp]
  nlinarith [h1, hp, hpow]

theorem avgCost_eq_riemann {n : ℕ} (hn : 0 < n) :
    avgCost n / (n : ℝ)
      = (∑ k ∈ Finset.range n, fBar ((k : ℝ) / (n : ℝ))) / (n : ℝ)
        - ((∑ k ∈ Finset.range n, Nat.gcd n k : ℕ) : ℝ) / (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hterm : ∀ k ∈ Finset.range n,
      ((algCost n k : ℕ) : ℝ)
        = (n : ℝ) * fBar ((k : ℝ) / (n : ℝ)) - ((Nat.gcd n k : ℕ) : ℝ) := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hkn : k ≤ n := le_of_lt hk
    have hk0 : (0 : ℝ) ≤ (k : ℝ) / (n : ℝ) := by positivity
    have hk1 : (k : ℝ) / (n : ℝ) ≤ 1 := by
      rw [div_le_one hnR]
      exact_mod_cast hkn
    rw [fBar_eq_fCost hk0 hk1]
    linarith [relation hn hkn]
  rw [avgCost, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Nat.cast_sum]
  field_simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **Theorem 10.**  `avgCost n / n → ∫₀¹ f`. -/
theorem solution :
    Tendsto (fun n : ℕ => avgCost n / (n : ℝ)) atTop (𝓝 (∫ x in (0 : ℝ)..1, fBar x)):= by
  have hgcd : Tendsto
      (fun n : ℕ => ((∑ k ∈ Finset.range n, Nat.gcd n k : ℕ) : ℝ) / (n : ℝ) ^ 2)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n : ℕ => 1 / (n : ℝ) + 2 * ((n.divisors.card : ℝ) / (n : ℝ)))
        atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
        tendsto_one_div_atTop_nhds_zero_nat
      have h2 : Tendsto (fun n : ℕ => 2 * ((n.divisors.card : ℝ) / (n : ℝ))) atTop (𝓝 (2 * 0)) :=
        tendsto_divisors_div.const_mul 2
      rw [mul_zero] at h2
      have h3 := h1.add h2
      rw [add_zero] at h3
      exact h3
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => by positivity) ?_ hlim
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hb : ((∑ k ∈ Finset.range n, Nat.gcd n k : ℕ) : ℝ)
        ≤ (n : ℝ) + 2 * ((n : ℝ) * (n.divisors.card : ℝ)) := by
      have := sum_gcd_range_le hn
      exact_mod_cast this
    rw [div_le_iff₀ (by positivity)]
    have hexp : (1 / (n : ℝ) + 2 * ((n.divisors.card : ℝ) / (n : ℝ))) * (n : ℝ) ^ 2
        = (n : ℝ) + 2 * ((n : ℝ) * (n.divisors.card : ℝ)) := by
      field_simp
    rw [hexp]
    exact hb
  have hcomb := tendsto_riemann_fBar.sub hgcd
  rw [sub_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (avgCost_eq_riemann hn).symm
