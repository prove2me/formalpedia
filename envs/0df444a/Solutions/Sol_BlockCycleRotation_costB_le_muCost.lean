-- Prove2me | solution 1 for BlockCycleRotation.costB_le_muCost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:14:12.439339+00:00
-- url     : https://prove2.me/submissions/89812d62-3fb9-4bd9-96e4-411b0622df66

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Buffer
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Theorems.Thm_BlockCycleRotation_muCost_rec_of_gt
import Mathlib

open Finset Filter Topology Real MeasureTheory BoxIntegral
open scoped ENNReal

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

theorem seg_zero (x : ℝ) : seg x 0 = x := by
  unfold seg
  simp

theorem bufDepth_eq_zero {β x : ℝ} (h : x ≤ β) : bufDepth β x = 0 :=
  Nat.eq_zero_of_le_zero (Nat.sInf_le (by rw [Set.mem_setOf_eq, seg_zero]; exact h))

/-- **The terminating branch.** -/
theorem psiBuf_of_le {β x : ℝ} (h : x ≤ β) : psiBuf β x = x := by
  rw [psiBuf, bufDepth_eq_zero h, seg_zero]
  simp

/-- **Equation (def-mu-nu).**  `μ(N,ℓ,β) - N = ℓ` when `ℓ ≤ β`, and otherwise
`2ℓ + μ(N',ℓ',β) - N'` for the subproblem `N' = N·Out(ℓ/N)`,
`ℓ' = N'·In(ℓ/N)`. -/
theorem muCost_rec_of_le {N l b : ℝ} (hN : 0 < N) (h : l ≤ b) :
    muCost N l b - N = l := by
  unfold muCost
  rw [psiBuf_of_le (by
    rw [div_le_div_iff_of_pos_right hN]
    exact h)]
  field_simp
  ring

@[simp]
theorem costB_zero (n b : ℕ) : costB n 0 b = 0 := by rw [costB]; simp

theorem costB_of_le {n k b : ℕ} (hk : k ≠ 0) (h : k ≤ b) : costB n k b = n + k := by
  rw [costB]; simp [hk, h]

theorem costB_of_gt {n k b : ℕ} (hk : k ≠ 0) (h : b < k) :
    costB n k b = (n / k + 1) * k + costB (k + n % k) (n % k) b := by
  rw [costB]; simp [hk, Nat.not_le.2 h]

/-- `N·Out(k/N)` is the next array length `n' = k + n % k`. -/
theorem mul_Outt_natCast {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    (n : ℝ) * Outt ((k : ℝ) / (n : ℝ)) = ((k + n % k : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : ((k : ℝ) / (n : ℝ)) ≠ 0 := by positivity
  have hinv : 1 / ((k : ℝ) / (n : ℝ)) = (n : ℝ) / (k : ℝ) := one_div_div _ _
  unfold Outt
  rw [if_neg hx, hinv, Int.fract_div_natCast_eq_div_natCast_mod]
  push_cast
  field_simp

/-- `n'·In(k/N)` is the next shift `k' = n % k`. -/
theorem mul_Inn_natCast {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    ((k + n % k : ℕ) : ℝ) * Inn ((k : ℝ) / (n : ℝ)) = ((n % k : ℕ) : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hx : ((k : ℝ) / (n : ℝ)) ≠ 0 := by positivity
  have hinv : 1 / ((k : ℝ) / (n : ℝ)) = (n : ℝ) / (k : ℝ) := one_div_div _ _
  unfold Inn
  rw [if_neg hx, hinv, Int.fract_div_natCast_eq_div_natCast_mod]
  have hden : (1 : ℝ) + ((n % k : ℕ) : ℝ) / (k : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

end BlockCycleRotation

open BlockCycleRotation in
/-- **Corollary, item 3.**  The buffered algorithm never uses more moves than
the continuous upper bound `μ`.  The two recursions agree step for step; the
inequality comes from the algorithm's extra base case `k = 0`. -/
theorem solution : ∀ k n b : ℕ, 0 < n → 0 < b → 2 * k ≤ n →
    ((costB n k b : ℕ) : ℝ) ≤ muCost (n : ℝ) (k : ℝ) (b : ℝ):= by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n b hn hb hkn
    have hN : (0 : ℝ) < n := by exact_mod_cast hn
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · subst hk0
      have h := muCost_rec_of_le (N := (n : ℝ)) (l := 0) (b := (b : ℝ)) hN (by positivity)
      rw [costB_zero]
      push_cast
      linarith
    rcases le_or_gt k b with hkb | hkb
    · have h := muCost_rec_of_le (N := (n : ℝ)) (l := (k : ℝ)) (b := (b : ℝ)) hN
        (by exact_mod_cast hkb)
      rw [costB_of_le hk0.ne' hkb]
      push_cast
      linarith
    · have hbR : (0 : ℝ) < b := by exact_mod_cast hb
      have hbkR : (b : ℝ) < (k : ℝ) := by exact_mod_cast hkb
      have hlR : 2 * (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
      have hrec := muCost_rec_of_gt hN hbR hbkR hlR
      rw [mul_Outt_natCast hn hk0] at hrec
      rw [mul_Inn_natCast hn hk0] at hrec
      -- the recursive call, via the induction hypothesis
      have hmod : n % k < k := Nat.mod_lt _ hk0
      have hIH := ih (n % k) hmod (k + n % k) b (by omega) hb (by omega)
      -- the discrete step `(⌊n/k⌋+1)k = n - n % k + k`
      have hdm : n / k * k + n % k = n := Nat.div_add_mod' n k
      have hstep : (((n / k + 1) * k : ℕ) : ℝ) = (n : ℝ) - ((n % k : ℕ) : ℝ) + (k : ℝ) := by
        have h1 : ((n / k * k + n % k : ℕ) : ℝ) = (n : ℝ) := by exact_mod_cast hdm
        push_cast at h1 ⊢
        linarith
      rw [costB_of_gt hk0.ne' hkb]
      push_cast
      push_cast at hstep hIH hrec
      linarith
