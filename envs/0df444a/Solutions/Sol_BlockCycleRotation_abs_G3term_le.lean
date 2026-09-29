-- Prove2me | solution 1 for BlockCycleRotation.abs_G3term_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:50:24.063286+00:00
-- url     : https://prove2.me/submissions/2749446a-91d1-4a7d-a009-ac3ccafffd3c

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem13
import Definitions.Def_BlockCycleRotation_TripleSum
import Theorems.Thm_BlockCycleRotation_inner_gt_estimate
import Mathlib

open Finset Real

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
/-- **The bound of Lemma 19 at one pair:** `|G₃| ≤ (|A| + |B|(Y-1))(1 + log a)`,
from the character estimate. -/
theorem solution {m d a a' : ℕ} (hm : 0 < m) (hd : 0 < d)
    (ha' : 1 ≤ a') (haa : a' < a) (hgcd : Nat.gcd a a' = 1) (hbulk : d * a * (a + a') ≤ m) :
    |G3term m d a a'|
      ≤ (|aCoeff m d a| + |bCoeff a a'| * ((gtBound m d a a' - 1 : ℕ) : ℝ))
          * (1 + Real.log a):= by
  have ha : 0 < a := by omega
  have hs : 0 < a + a' := by omega
  have hda2 : d * a * a < m := by nlinarith
  have hrange : ∀ b' ∈ Finset.Ico 1 (gtBound m d a a'), a' * b' ≤ m := by
    intro b' hb'
    have := (mem_gtRange hm hs ha' hda2).1 hb'
    omega
  obtain ⟨c, hc⟩ := inner_gt_estimate (m := m) (d := d) (a := a) (a' := a') ha hgcd
    (gtBound m d a a') hrange
  exact hc
