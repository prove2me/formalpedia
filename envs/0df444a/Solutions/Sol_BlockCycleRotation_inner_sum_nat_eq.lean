-- Prove2me | solution 1 for BlockCycleRotation.inner_sum_nat_eq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:12:38.037284+00:00
-- url     : https://prove2.me/submissions/d1100aa7-6067-4380-9b83-aa1c212150c6

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
/-- **The inner sum of the triple sum, as an arithmetic-progression sum.**

The natural-number inner sum `∑ (m - a'b')/a`, taken over `b'` satisfying the
divisibility condition, is the real sum of the linear function
`m/a - (a'/a)·b'` over an arithmetic progression modulo `a` — the exact shape
`sum_ap_sub_main_le_log` estimates. -/
theorem solution {m a a' : ℕ} (ha : 0 < a) (hgcd : Nat.gcd a a' = 1) :
    ∃ c : ℤ, ∀ U : ℕ, (∀ b' ∈ Finset.Ico 1 U, a' * b' ≤ m) →
      ((∑ b' ∈ (Finset.Ico 1 U).filter (fun b' => a ∣ (m - a' * b')),
          (m - a' * b') / a : ℕ) : ℝ)
        = ∑ b' ∈ Finset.Ico 1 U,
            (if (a : ℤ) ∣ ((b' : ℤ) - c) then ((m : ℝ) / a - (a' : ℝ) / a * b') else 0):= by
  obtain ⟨c, hc⟩ := exists_residue (m := m) hgcd
  refine ⟨c, fun U hU => ?_⟩
  rw [Finset.sum_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun b' hb' => ?_
  have hle : a' * b' ≤ m := hU b' hb'
  -- the two divisibility conditions agree
  have hiff : (a ∣ (m - a' * b')) ↔ ((a : ℤ) ∣ ((b' : ℤ) - c)) := by
    rw [← hc (b' : ℤ)]
    constructor
    · intro h
      have : ((a : ℤ)) ∣ (((m - a' * b' : ℕ)) : ℤ) := Int.natCast_dvd_natCast.2 h
      rwa [Nat.cast_sub hle, Nat.cast_mul] at this
    · intro h
      have h2 : ((a : ℤ)) ∣ (((m - a' * b' : ℕ)) : ℤ) := by
        rwa [Nat.cast_sub hle, Nat.cast_mul]
      exact Int.natCast_dvd_natCast.1 h2
  by_cases hd : a ∣ (m - a' * b')
  · rw [if_pos hd, if_pos (hiff.1 hd)]
    have hmul : a * ((m - a' * b') / a) = m - a' * b' := Nat.mul_div_cancel' hd
    have hreal : ((a : ℝ)) * (((m - a' * b') / a : ℕ) : ℝ) = (m : ℝ) - (a' : ℝ) * b' := by
      have := congrArg (Nat.cast : ℕ → ℝ) hmul
      push_cast [Nat.cast_sub hle] at this
      linarith
    have hane : ((a : ℝ)) ≠ 0 := by positivity
    field_simp at hreal ⊢
    linarith
  · rw [if_neg hd, if_neg (fun h => hd (hiff.2 h))]
    simp
