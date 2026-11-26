-- Prove2me | solution 1 for Erdos287.factorial_prime_rung
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T05:06:14.320737+00:00
-- url     : https://prove2.me/submissions/c38773fb-21ec-4489-94a7-c55015855a85

import Mathlib
import Theorems.Thm_Erdos287_prime_power_pair_excludes_band

set_option autoImplicit false

private theorem cofactorSum_le_factorial (B : ℕ) :
    (∑ j ∈ Finset.Icc 1 B, Nat.lcmUpto B / j) ≤ B * B.factorial := by
  have hL : Nat.lcmUpto B ≤ B.factorial :=
    Nat.le_of_dvd (Nat.factorial_pos B) (Nat.lcmUpto_dvd_factorial B)
  calc
    _ ≤ ∑ _j ∈ Finset.Icc 1 B, B.factorial :=
      Finset.sum_le_sum fun j _ => (Nat.div_le_self _ j).trans hL
    _ = B * B.factorial := by simp

/-- An adjacent pair with factorial cofactor bounds certifies a finite
interval of possible maximum denominators. -/
theorem solution (k : ℕ) (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (x p q B D : ℕ) (hp : p.Prime) (hq : q.Prime) (hdivp : p ∣ x) (hdivq : q ∣ x + 1)
    (hfp : B * B.factorial < p) (hfq : D * D.factorial < q)
    (hlo : x + 2 ≤ f (k - 1))
    (hhip : f (k - 1) < (B + 1) * p) (hhiq : f (k - 1) < (D + 1) * q)
    (hband : 2 * f (k - 1) + 20 ≤ 5 * x) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  have hx : 0 < x := by omega
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hbandR : 2 * (f (k - 1) : ℝ) + 20 ≤ 5 * (x : ℝ) := by exact_mod_cast hband
  have hreal : (f (k - 1) : ℝ) < Real.exp 1 * x := by
    calc
      _ < (5 / 2 : ℝ) * x := by linarith
      _ < Real.exp 1 * x := by
        exact mul_lt_mul_of_pos_right (by linarith [Real.exp_one_gt_d9]) hxR
  have cofactor_le (a : ℕ) : a ≤ a * a.factorial := by
    simpa using Nat.mul_le_mul_left a (Nat.succ_le_iff.mpr (Nat.factorial_pos a))
  exact Erdos287.prime_power_pair_excludes_band k hk f hf1 hmono hsum x hx (by omega)
    hreal p q 1 1 B D hp hq le_rfl le_rfl
    (by simpa using hdivp) (by simpa using hdivq)
    ((cofactor_le B).trans_lt hfp) ((cofactor_le D).trans_lt hfq)
    (by simpa using hhip) (by simpa using hhiq)
    ((cofactorSum_le_factorial B).trans_lt hfp) ((cofactorSum_le_factorial D).trans_lt hfq)

