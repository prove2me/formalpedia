-- Prove2me | solution 1 for BlockCycleRotation.tsum_telescope
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:37:08.570032+00:00
-- url     : https://prove2.me/submissions/58e57404-637e-4917-9b52-7e8251ebc3e6

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_telescope_partial
import Theorems.Thm_BlockCycleRotation_tendsto_window
import Mathlib

open Real Finset Filter Topology

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
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- The telescoping series `∑_j [1/(j+1) - 1/(j+n+1)]` sums to `H_n`. -/
theorem solution (n : ℕ) :
    ∑' j : ℕ, (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1))
      = ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1):= by
  have hsum : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1)) := by
    have hg : Summable (fun j : ℕ => (n : ℝ) * (1 / ((j : ℝ) + 1) ^ 2)) := by
      have h : Summable (fun j : ℕ => 1 / ((j : ℝ) + 1) ^ 2) := by
        have h0 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) := by
          rw [Real.summable_one_div_nat_pow]; norm_num
        refine ((summable_nat_add_iff 1).2 h0).congr fun j => ?_
        push_cast; ring
      exact h.mul_left _
    refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hg
    · have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
      have h1 : 1 / ((j : ℝ) + (n : ℝ) + 1) ≤ 1 / ((j : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    · have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hjn : (0 : ℝ) < (j : ℝ) + (n : ℝ) + 1 := by positivity
      have key : 1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1)
          = (n : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + (n : ℝ) + 1)) := by
        field_simp
        ring
      have hr : (n : ℝ) * (1 / ((j : ℝ) + 1) ^ 2) = (n : ℝ) / ((j : ℝ) + 1) ^ 2 := by ring
      rw [key, hr]
      gcongr
      nlinarith
  refine (hsum.hasSum_iff_tendsto_nat.2 ?_).tsum_eq
  have heq : (fun N : ℕ => ∑ j ∈ Finset.range N,
        (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1)))
      =ᶠ[atTop] (fun N : ℕ => (∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1))
        - ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)) := by
    filter_upwards [eventually_ge_atTop n] with N hN
    exact telescope_partial n N hN
  refine Tendsto.congr' heq.symm ?_
  have hlim : Tendsto (fun N : ℕ => (∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1))
      - ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)) atTop
      (𝓝 ((∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1)) - 0)) :=
    tendsto_const_nhds.sub (tendsto_window n)
  rw [sub_zero] at hlim
  exact hlim
