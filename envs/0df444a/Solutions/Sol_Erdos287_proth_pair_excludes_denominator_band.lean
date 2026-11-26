-- Prove2me | solution 1 for Erdos287.proth_pair_excludes_denominator_band
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T09:38:09.301584+00:00
-- url     : https://prove2.me/submissions/bdbe2b67-981d-4c27-b8df-99ce2166e6c5

import Mathlib
import Theorems.Thm_Erdos287_proth_prime_certificate
import Theorems.Thm_Erdos287_factorial_prime_rung

set_option autoImplicit false

/-- One witness for each Proth number in a pair excludes a full interval of
possible maximal denominators. -/
theorem solution (r e a b k : ℕ) (hr : 0 < r) (hrsmall : r < 2 ^ (e + 1))
    (hk : 2 ≤ k) (f : ℕ → ℕ)
    (hf1 : ∀ i, i < k → 1 < f i)
    (hmono : ∀ i j, i < j → j < k → f i < f j)
    (hsum : ∑ i ∈ Finset.range k, (1 : ℚ) / f i = 1) :
    let P := r * 2 ^ (e + 1) + 1
    let Q := r * 2 ^ (e + 2) + 1
    let M := f (k - 1)
    96 < P → (a : ZMod P) ^ (r * 2 ^ e) = -1 →
    (b : ZMod Q) ^ (r * 2 ^ (e + 1)) = -1 →
    Q + 2 ≤ M → 2 * M + 20 ≤ 5 * Q →
    ∃ i, i + 1 < k ∧ 3 ≤ f (i + 1) - f i := by
  intro P Q M hP ha hb hlo hhi
  have hPprime : P.Prime := Erdos287.proth_prime_certificate r e a hr hrsmall ha
  have hre : r < 2 ^ (e + 1 + 1) := hrsmall.trans_le
    (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hQprime : Q.Prime := Erdos287.proth_prime_certificate r (e + 1) b hr hre hb
  have hrel : Q + 1 = 2 * P := by
    dsimp [P, Q]
    rw [show (2 : ℕ) ^ (e + 2) = 2 ^ (e + 1) * 2 by rw [pow_succ]]
    ring
  exact Erdos287.factorial_prime_rung k hk f hf1 hmono hsum Q Q P 2 4
    hQprime hPprime dvd_rfl ⟨2, by omega⟩
    (by norm_num [Nat.factorial]; omega) (by norm_num [Nat.factorial]; omega)
    hlo (by omega) (by omega) hhi

