-- Prove2me | solution 1 for BlockCycleRotation.inner_gt_sum_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:19:05.35798+00:00
-- url     : https://prove2.me/submissions/6dc832f8-afe2-4315-afd9-362787d4a65a

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_exists_residue
import Mathlib

open Real Finset

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
/-- The inner sum of the restricted triple sum, as an arithmetic-progression sum
with the paper's coefficients `A = d·a + m/a` and `B = -a'/a`. -/
theorem solution {m d a a' : ℕ} (ha : 0 < a) (hgcd : Nat.gcd a a' = 1) :
    ∃ c : ℤ, ∀ U : ℕ, (∀ b' ∈ Finset.Ico 1 U, a' * b' ≤ m) →
      ((∑ b' ∈ (Finset.Ico 1 U).filter (fun b' => a ∣ (m - a' * b')),
          (d * a + (m - a' * b') / a) : ℕ) : ℝ)
        = ∑ b' ∈ Finset.Ico 1 U,
            (if (a : ℤ) ∣ ((b' : ℤ) - c) then
              ((((d * a : ℕ) : ℝ) + (m : ℝ) / a) + (-(a' : ℝ) / a) * b') else 0):= by
  obtain ⟨c, hc⟩ := exists_residue (m := m) hgcd
  refine ⟨c, fun U hU => ?_⟩
  rw [Finset.sum_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun b' hb' => ?_
  have hle : a' * b' ≤ m := hU b' hb'
  have hiff : (a ∣ (m - a' * b')) ↔ ((a : ℤ) ∣ ((b' : ℤ) - c)) := by
    rw [← hc (b' : ℤ)]
    constructor
    · intro h
      have h2 : ((a : ℤ)) ∣ (((m - a' * b' : ℕ)) : ℤ) := Int.natCast_dvd_natCast.2 h
      rwa [Nat.cast_sub hle, Nat.cast_mul] at h2
    · intro h
      have h2 : ((a : ℤ)) ∣ (((m - a' * b' : ℕ)) : ℤ) := by
        rwa [Nat.cast_sub hle, Nat.cast_mul]
      exact Int.natCast_dvd_natCast.1 h2
  by_cases hd : a ∣ (m - a' * b')
  · rw [if_pos hd, if_pos (hiff.1 hd)]
    have hmul : a * ((m - a' * b') / a) = m - a' * b' := Nat.mul_div_cancel' hd
    have hreal : ((a : ℝ)) * (((m - a' * b') / a : ℕ) : ℝ) = (m : ℝ) - (a' : ℝ) * b' := by
      have h3 := congrArg (Nat.cast : ℕ → ℝ) hmul
      push_cast [Nat.cast_sub hle] at h3
      linarith
    have hane : ((a : ℝ)) ≠ 0 := by positivity
    push_cast
    field_simp at hreal ⊢
    linarith
  · rw [if_neg hd, if_neg (fun h => hd (hiff.2 h))]
    simp
