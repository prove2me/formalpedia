-- Prove2me | solution 1 for BlockCycleRotation.gtBound_bulk
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:24:31.553153+00:00
-- url     : https://prove2.me/submissions/e8b9a59b-bb50-45d9-8716-464d8bf4af24

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
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

/-- **On the bulk branch, the first constraint implies the second.** -/
theorem bulk_second_of_first {m d a a' b' : ℕ} (ha : 0 < a) (ha' : 0 < a')
    (hbulk : d * a * (a + a') ≤ m) (h2 : (a + a') * b' < m) :
    a' * b' + d * a * a < m := by
  have haa : 0 < a + a' := by omega
  have key : (a + a') * (a' * b' + d * a * a) < (a + a') * m := by
    have e1 : (a + a') * (a' * b' + d * a * a)
        = a' * ((a + a') * b') + a * (d * a * (a + a')) := by ring
    have h3 : a' * ((a + a') * b') < a' * m := by nlinarith
    have h4 : a * (d * a * (a + a')) ≤ a * m := Nat.mul_le_mul_left a hbulk
    have e2 : (a + a') * m = a' * m + a * m := by ring
    omega
  exact Nat.lt_of_mul_lt_mul_left key

end BlockCycleRotation

open BlockCycleRotation in
/-- On the bulk branch the range of `b'` is cut by `(a+a')·b' < m` alone. -/
theorem solution {m d a a' : ℕ} (hm : 0 < m) (ha : 0 < a) (ha' : 0 < a')
    (hda : d * a * a < m) (hbulk : d * a * (a + a') ≤ m) :
    Finset.Ico 1 (gtBound m d a a') = Finset.Ico 1 ((m - 1) / (a + a') + 1):= by
  ext b'
  rw [mem_gtRange hm (by omega) ha' hda, Finset.mem_Ico, Nat.lt_succ_iff,
    Nat.le_div_iff_mul_le (by omega : 0 < a + a'), Nat.mul_comm b' (a + a')]
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩
    have h2' : (a + a') * b' < m := by omega
    exact ⟨h1, h2', bulk_second_of_first ha ha' hbulk h2'⟩
