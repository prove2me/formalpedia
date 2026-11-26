-- Prove2me | solution 1 for FirstPassageLinearTransport.targetScale_rpow_neg_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:09:03.705562+00:00
-- url     : https://prove2.me/submissions/aacb34ee-cfc6-4067-8599-2f57ddf337cd

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution {r D : ℝ} {M : ℕ}
    (hr : 0 ≤ r) (hD0 : 0 ≤ D) (hD1 : D ≤ 1) :
    (targetScale r M : ℝ) ^ (-D) ≤
      2 * Real.exp (-(r * D * M * Real.log 2)) := by
  have hx0 : 0 ≤ r * (M : ℝ) := mul_nonneg hr (Nat.cast_nonneg M)
  have hfloor : r * (M : ℝ) - 1 < (⌊r * (M : ℝ)⌋₊ : ℝ) :=
    Nat.sub_one_lt_floor _
  have hExp :
      -D * (⌊r * (M : ℝ)⌋₊ : ℝ) ≤ D - r * D * M := by
    nlinarith
  calc
    (targetScale r M : ℝ) ^ (-D) =
        (2 : ℝ) ^ (-D * (⌊r * (M : ℝ)⌋₊ : ℝ)) := by
      unfold targetScale
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    _ ≤ (2 : ℝ) ^ (D - r * D * M) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
    _ ≤ (2 : ℝ) ^ (1 - r * D * M) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 2 * Real.exp (-(r * D * M * Real.log 2)) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
        show Real.log 2 * (1 - r * D * M) =
          Real.log 2 + -(r * D * M * Real.log 2) by ring,
        Real.exp_add, Real.exp_log (by norm_num)]
end FirstPassageLinearTransport
