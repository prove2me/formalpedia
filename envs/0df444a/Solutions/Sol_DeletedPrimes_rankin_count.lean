-- Prove2me | solution 1 for DeletedPrimes.rankin_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T21:59:26.847052+00:00
-- url     : https://prove2.me/submissions/04908c77-d152-4050-9d4c-862da9c024fa

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_Legendre

set_option autoImplicit false
open Real Filter Topology
open DeletedPrimes
noncomputable section
open Classical
variable {S : Set ℕ}
namespace DeletedPrimes
theorem _root_.solution {σ : ℝ} (hsum : Summable fun d : ℕ => |(muS S d : ℝ)| * (d : ℝ) ^ (-σ))
    (hσ : 0 ≤ σ) {Z : ℝ} (hZ : 1 ≤ Z) :
    ∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, |(muS S d : ℝ)| ≤ unitSum S σ * Z ^ σ := by
  have hZ0 : 0 < Z := by linarith
  calc ∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, |(muS S d : ℝ)|
      ≤ ∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, |(muS S d : ℝ)| * (d : ℝ) ^ (-σ) * Z ^ σ := by
        refine Finset.sum_le_sum fun d hd => ?_
        obtain ⟨hd1, hdZ⟩ := Finset.mem_Icc.mp hd
        have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
        have hdZ' : (d : ℝ) ≤ Z := le_trans (by exact_mod_cast hdZ) (Nat.floor_le hZ0.le)
        have : 1 ≤ (d : ℝ) ^ (-σ) * Z ^ σ := by
          rw [Real.rpow_neg hd0.le, ← div_eq_inv_mul, le_div_iff₀ (Real.rpow_pos_of_pos hd0 _),
            one_mul]
          exact Real.rpow_le_rpow hd0.le hdZ' hσ
        rw [mul_assoc]
        exact le_mul_of_one_le_right (abs_nonneg _) this
    _ = (∑ d ∈ Finset.Icc 1 ⌊Z⌋₊, |(muS S d : ℝ)| * (d : ℝ) ^ (-σ)) * Z ^ σ := by
        rw [Finset.sum_mul]
    _ ≤ unitSum S σ * Z ^ σ := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hZ0.le _)
        exact hsum.sum_le_tsum _ fun d _ =>
          mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
end DeletedPrimes
