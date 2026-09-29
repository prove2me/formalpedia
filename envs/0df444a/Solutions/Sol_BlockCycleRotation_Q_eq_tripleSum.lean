-- Prove2me | solution 1 for BlockCycleRotation.Q_eq_tripleSum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:10:43.212576+00:00
-- url     : https://prove2.me/submissions/7562f0b0-02bd-4026-a037-246e44cbb5de

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_sum_snd_quadruplesQ
import Theorems.Thm_BlockCycleRotation_sum_snd_quadruplesAll_eq
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
/-- **The triple sum.**  `Q(n)` as a sum over divisors `d ∣ n`, coprime pairs
`a > a' ≥ 1`, and `b'` subject to `(a+a')b' < n/d` and `n/d ≡ a'b' (mod a)`. -/
theorem solution {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ quadruplesQ n, q.2.1
      = ∑ d ∈ n.divisors, ∑ t ∈ coprimeTriples (n / d), (n / d - t.2.1 * t.2.2) / t.1:= by
  rw [sum_snd_quadruplesQ hn]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  have : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hd0
  exact sum_snd_quadruplesAll_eq this
