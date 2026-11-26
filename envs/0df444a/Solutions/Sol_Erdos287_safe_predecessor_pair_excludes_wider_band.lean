-- Prove2me | solution 1 for Erdos287.safe_predecessor_pair_excludes_wider_band
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T09:42:52.546546+00:00
-- url     : https://prove2.me/submissions/159c5831-4a0f-4d3f-852c-9d90a7f66710

import Mathlib
import Theorems.Thm_Erdos287_prime_power_pair_excludes_band

open Finset

set_option autoImplicit false

/-- The harmonic endpoint estimate extends a pair-supported band to a
factor of 2.7 above the first omitted integer. -/
theorem solution (p q k : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hlarge : 137 < p) (hrel : q + 1 = 2 * p)
    (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1)
    (hlo : q + 1 ≤ f (k - 1)) (hhi : 10 * f (k - 1) ≤ 27 * q) :
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  have hqpos : 0 < q := hq.pos
  have hexp : (27 / 10 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hcast : (10 : ℝ) * f (k - 1) ≤ 27 * (q : ℝ) := by exact_mod_cast hhi
  have hratio : (f (k - 1) : ℝ) < Real.exp 1 * q := by
    have h : (f (k - 1) : ℝ) ≤ (27 / 10 : ℝ) * q := by linarith only [hcast]
    exact h.trans_lt (mul_lt_mul_of_pos_right hexp (by exact_mod_cast hqpos))
  have hsleft : (∑ j ∈ Finset.Icc 1 2, Nat.lcmUpto 2 / j) = 3 := by decide
  have hsright : (∑ j ∈ Finset.Icc 1 5, Nat.lcmUpto 5 / j) = 137 := by decide
  exact Erdos287.prime_power_pair_excludes_band k hk f hf1 hmono hsum q hqpos hlo hratio
    q p 1 1 2 5 hq hp le_rfl le_rfl
    (by simp) (by simp [hrel]) (by omega) (by omega)
    (by simp only [pow_one]; omega) (by simp only [pow_one]; omega)
    (hsleft ▸ (show 3 < q by omega)) (hsright ▸ hlarge)

