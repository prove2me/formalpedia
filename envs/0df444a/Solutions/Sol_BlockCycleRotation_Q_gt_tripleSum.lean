-- Prove2me | solution 1 for BlockCycleRotation.Q_gt_tripleSum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:16:42.518278+00:00
-- url     : https://prove2.me/submissions/f6755e7c-20dd-4c53-938c-c576e8cb5ccc

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_sum_QGT_classify
import Theorems.Thm_BlockCycleRotation_sum_quadGT_eq
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
/-- **The restricted triple sum.**  This is the paper's triple sum: over
divisors `d ∣ n`, coprime pairs `a > a' ≥ 1`, and `b'` subject to
`(a+a')b' < n/d`, `n/d ≡ a'b' (mod a)` and `n/d - a'b' > d·a²`. -/
theorem solution {n : ℕ} (hn : 0 < n) :
    ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1)
      = ∑ d ∈ n.divisors, ∑ t ∈ gtTriples (n / d) d,
          (d * t.1 + (n / d - t.2.1 * t.2.2) / t.1):= by
  rw [sum_QGT_classify hn]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hdn, -⟩ := Nat.mem_divisors.1 hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn hn
  exact sum_quadGT_eq (Nat.div_pos (Nat.le_of_dvd hn hdn) hd0)
