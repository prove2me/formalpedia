-- Prove2me | solution 1 for FirstPassageLinearTransport.quadratic_startup_exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:24:00.789635+00:00
-- url     : https://prove2.me/submissions/284a95c3-da4e-427f-9c6d-710b476dd3bd

import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Theorems.Thm_FirstPassageLinearTransport_maximalBarrierC0_pos

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M : ℕ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hsmall : ¬(4 ≤ M ∧ 2 ≤ t * M)) :
    maximalBarrierC0 * t ^ 2 * M ≤ 4 * maximalBarrierC0 := by
  rcases not_and_or.mp hsmall with hM | htM
  · have hMR : (M : ℝ) ≤ 4 := by exact_mod_cast (by omega : M ≤ 4)
    have ht2 : t ^ 2 ≤ (1 : ℝ) := by nlinarith [sq_nonneg t]
    have hprod : t ^ 2 * (M : ℝ) ≤ 1 * 4 :=
      mul_le_mul ht2 hMR (Nat.cast_nonneg M) (by norm_num)
    nlinarith [maximalBarrierC0_pos.le]
  · have htMR : t * (M : ℝ) ≤ 2 := le_of_not_ge htM
    have hprod : t * (t * (M : ℝ)) ≤ 1 * 2 :=
      mul_le_mul ht1 htMR
        (mul_nonneg ht0.le (Nat.cast_nonneg M)) (by norm_num)
    nlinarith [maximalBarrierC0_pos.le]
end FirstPassageLinearTransport
