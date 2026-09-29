-- Prove2me | solution 1 for BlockCycleRotation.small_pair_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:25:32.634144+00:00
-- url     : https://prove2.me/submissions/8d0c38d6-901d-4ae0-96dd-7adcf0a5cdb7

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_card_dvd_filter_le
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

theorem mem_gtRange {m d a a' b' : ℕ} (hm : 0 < m) (haa : 0 < a + a') (ha' : 0 < a')
    (hda : d * a * a < m) :
    b' ∈ Finset.Ico 1 (gtBound m d a a')
      ↔ (1 ≤ b' ∧ (a + a') * b' < m ∧ a' * b' + d * a * a < m) := by
  rw [Finset.mem_Ico, gtBound, lt_min_iff, Nat.lt_succ_iff, Nat.lt_succ_iff,
    Nat.le_div_iff_mul_le haa, Nat.le_div_iff_mul_le ha',
    Nat.mul_comm b' (a + a'), Nat.mul_comm b' a']
  omega

end BlockCycleRotation

open BlockCycleRotation in
/-- **The per-pair bound on the small branch.** -/
theorem solution {m d a a' : ℕ} (ha : 0 < a) (ha' : 0 < a') (hgcd : Nat.gcd a a' = 1)
    (hda : d * a * a < m) (haa : a' < a) (hsmall : ¬ (d * a * (a + a') ≤ m)) :
    ∑ b' ∈ (Finset.Ico 1 (gtBound m d a a')).filter (fun b' => a ∣ (m - a' * b')),
        (d * a + (m - a' * b') / a)
      ≤ (2 * d + 2) * (2 * (m / a)):= by
  have hm : 0 < m := by omega
  have haa0 : 0 < a + a' := by omega
  -- every `b'` in range has `a' * b' ≤ m`
  have hU : ∀ b ∈ Finset.Ico 1 (gtBound m d a a'), a' * b ≤ m := by
    intro b hb
    obtain ⟨-, -, h3⟩ := (mem_gtRange hm haa0 ha' hda).1 hb
    omega
  -- the count is at most `2d + 2`
  have hsq : m < 2 * (d * a * a) := by nlinarith
  have hcard : (((Finset.Ico 1 (gtBound m d a a')).filter
      (fun b' => a ∣ (m - a' * b'))).card) ≤ 2 * d + 2 := by
    refine le_trans (card_dvd_filter_le ha hgcd hU) ?_
    have hb1 : gtBound m d a a' ≤ (m - 1) / (a + a') + 1 := min_le_left _ _
    have hb2 : gtBound m d a a' ≤ (m - 1) / a + 1 :=
      le_trans hb1 (by
        have : (m - 1) / (a + a') ≤ (m - 1) / a := Nat.div_le_div_left (by omega) ha
        omega)
    have hb3 : gtBound m d a a' / a ≤ ((m - 1) / a + 1) / a := Nat.div_le_div_right hb2
    have hb4 : ((m - 1) / a + 1) / a ≤ (m - 1) / (a * a) + 1 := by
      rw [← Nat.div_div_eq_div_mul]
      have h2 : ((m - 1) / a + 1) / a ≤ ((m - 1) / a + a) / a :=
        Nat.div_le_div_right (by omega)
      have h3 : ((m - 1) / a + a) / a = (m - 1) / a / a + 1 := Nat.add_div_right _ ha
      omega
    have hb5 : (m - 1) / (a * a) ≤ 2 * d := by
      have heq : 2 * (d * a * a) = 2 * d * (a * a) := by ring
      have h1 : m - 1 ≤ 2 * d * (a * a) := by omega
      calc (m - 1) / (a * a) ≤ (2 * d * (a * a)) / (a * a) := Nat.div_le_div_right h1
        _ = 2 * d := Nat.mul_div_cancel _ (by positivity)
    omega
  -- every summand is at most `2 * (m / a)`
  have hterm : ∀ b' ∈ (Finset.Ico 1 (gtBound m d a a')).filter (fun b' => a ∣ (m - a' * b')),
      d * a + (m - a' * b') / a ≤ 2 * (m / a) := by
    intro b' _
    have h1 : d * a ≤ m / a := by
      refine (Nat.le_div_iff_mul_le ha).2 ?_
      nlinarith
    have h2 : (m - a' * b') / a ≤ m / a := Nat.div_le_div_right (by omega)
    omega
  calc ∑ b' ∈ (Finset.Ico 1 (gtBound m d a a')).filter (fun b' => a ∣ (m - a' * b')),
        (d * a + (m - a' * b') / a)
      ≤ ∑ _b' ∈ (Finset.Ico 1 (gtBound m d a a')).filter (fun b' => a ∣ (m - a' * b')),
          2 * (m / a) := Finset.sum_le_sum hterm
    _ = (((Finset.Ico 1 (gtBound m d a a')).filter
          (fun b' => a ∣ (m - a' * b'))).card) * (2 * (m / a)) := by
        rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (2 * d + 2) * (2 * (m / a)) := Nat.mul_le_mul_right _ hcard
