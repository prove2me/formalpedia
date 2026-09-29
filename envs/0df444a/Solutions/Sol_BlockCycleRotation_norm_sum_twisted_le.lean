-- Prove2me | solution 1 for BlockCycleRotation.norm_sum_twisted_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:38:32.485648+00:00
-- url     : https://prove2.me/submissions/7f98c343-9389-45aa-87e5-4f2638d00835

import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_e_root_ne_one
import Theorems.Thm_BlockCycleRotation_two_div_norm_le
import Theorems.Thm_BlockCycleRotation_sum_inv_min_le
import Theorems.Thm_BlockCycleRotation_norm_linear_geom_sum_le
import Mathlib

open Real Finset

namespace BlockCycleRotation

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

/-- The inner sum at a nontrivial `a`-th root of unity. -/
theorem norm_linear_geom_sum_root_le {a m : ℕ} (h0 : 0 < m) (hma : m < a) (A B : ℂ) (T : ℕ) :
    ‖∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖
      ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * ((a : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ))) := by
  refine (norm_linear_geom_sum_le (e_root_ne_one h0 hma) A B T).trans ?_
  have hK : (0 : ℝ) ≤ ‖A‖ + ‖B‖ * (T - 1 : ℕ) := by positivity
  exact mul_le_mul_of_nonneg_left (two_div_norm_le h0 hma) hK

end BlockCycleRotation

open BlockCycleRotation in
/-- **The error term of §4.**  Summing the inner sums over the nontrivial
characters, against arbitrary weights of modulus at most one, costs a harmonic
sum — this is where the `log a` of Lemma 18 comes from. -/
theorem solution {a : ℕ} (A B : ℂ) (T : ℕ) (w : ℕ → ℂ) (hw : ∀ m, ‖w m‖ ≤ 1) :
    ‖∑ m ∈ Finset.Ico 1 a, w m * ∑ b ∈ Finset.Ico 1 T,
        (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖
      ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (a : ℝ) * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ):= by
  have hK : (0 : ℝ) ≤ ‖A‖ + ‖B‖ * (T - 1 : ℕ) := by positivity
  -- bound each term
  have hterm : ∀ m ∈ Finset.Ico 1 a,
      ‖w m * ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖
        ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * ((a : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ))) := by
    intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hm
    rw [norm_mul]
    calc ‖w m‖ * ‖∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖
        ≤ 1 * ‖∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖ := by
          gcongr
          exact hw m
      _ = ‖∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖ := one_mul _
      _ ≤ _ := norm_linear_geom_sum_root_le h1 h2 A B T
  -- pull the constants out of the sum
  have hpull : ∑ m ∈ Finset.Ico 1 a,
        (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * ((a : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ)))
      = (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (a : ℝ)
          * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => by ring
  -- the harmonic bound
  have hhalf : ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ))
      ≤ ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) := by
    have h1 : ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ))
        = (1 / 2) * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / ((min m (a - m) : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    have h2 := sum_inv_min_le a
    rw [h1]
    linarith
  calc ‖∑ m ∈ Finset.Ico 1 a, w m * ∑ b ∈ Finset.Ico 1 T,
          (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖
      ≤ ∑ m ∈ Finset.Ico 1 a,
          ‖w m * ∑ b ∈ Finset.Ico 1 T, (A + B * b) * e (2 * π * (m : ℝ) / a) ^ b‖ :=
        norm_sum_le _ _
    _ ≤ ∑ m ∈ Finset.Ico 1 a,
          (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * ((a : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (a : ℝ)
          * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (2 * ((min m (a - m) : ℕ) : ℝ)) := hpull
    _ ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (a : ℝ) * ∑ m ∈ Finset.Ico 1 a, (1 : ℝ) / (m : ℝ) := by
        have hpos : (0 : ℝ) ≤ (‖A‖ + ‖B‖ * (T - 1 : ℕ)) * (a : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left hhalf hpos
