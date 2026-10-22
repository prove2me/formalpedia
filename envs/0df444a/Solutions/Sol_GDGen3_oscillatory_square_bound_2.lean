-- Prove2me | solution 2 for GDGen3.oscillatory_square_bound
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T12:01:04.57183+00:00
-- url     : https://prove2.me/submissions/4b26012c-8366-4a0a-b5ac-7aaebfabdcf0

import Mathlib
import Definitions.Def_GDGen3Base
import Definitions.Def_GDGen3RootBase
import Theorems.Thm_GDGen3_certificate_identity_explicit_roots
import Theorems.Thm_GDGen3_certificate_sum_nonneg

noncomputable section

open Finset

open GDGen3

theorem solution
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1) (N : ℕ) (hN : 1 ≤ N)
    (hbranch : 1 / r ^ N ≤ 1 + (N : ℝ) * (1 + r))
    (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (R : ℕ → ℝ) (X0 : ℝ)
    (hP : ∀ i j, P i j = P j i)
    (hQ : ∀ i j, i ≤ N → j ≤ N → i ≠ j → 0 ≤ Qv (1 + r) f P i j)
    (hstar : ∀ i, i ≤ N → 0 ≤ -f i + gself (1 + r) R P i - (1 / 2) * P i i)
    (hto : ∀ i, i ≤ N → 0 ≤ f i - (1 / 2) * P i i)
    (hresidual : 0 ≤ (X0 - 2 * (1 + r) * (∑ i ∈ range N, R i)
        + (1 + r) ^ 2 * (∑ i ∈ range N, ∑ j ∈ range N, P i j))
      - 2 * gself (1 + r) R P N + P N N) :
    P N N ≤ r ^ (2 * N) * X0 := by
  have hid := certificate_identity_explicit_roots r N hN hr hr1 f P R X0 hP
  have hn := certificate_sum_nonneg r hr hr1 N hN hbranch f P R hQ hstar hto
  rw [hid] at hn
  unfold certRhs at hn
  have hp := mul_nonneg (show 0 ≤ r ^ (2 * N) by positivity) hresidual
  linarith
