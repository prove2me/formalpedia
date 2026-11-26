-- Prove2me | solution 1 for FirstPassageLinearTransport.transportedBad_le_paid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:42:25.168847+00:00
-- url     : https://prove2.me/submissions/4ced9b7c-5026-4d53-961c-a44dbb8287d8

import Definitions.Def_FirstPassageLinearTransport_BarrierDensity
import Definitions.Def_FirstPassageLinearTransport_Transport
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Theorems.Thm_FirstPassageLinearTransport_square_exp_payment
import Theorems.Thm_FirstPassageLinearTransport_transportedBad_le
import Theorems.Thm_FirstPassageLinearTransport_transportGap_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_C_pos
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta C D chi : ℝ} (p : StageSetup r eta)
    (S : Set ℕ) (hS : PowerDense S C D)
    (hchi : chi < r) {M : ℕ} (hM : p.M0 ≤ M) :
    ((transportedSources M (targetScale r M) M
      (badTarget S (targetScale r M))).card : ℝ) ≤
      (20 / transportGap r chi ^ 2) * C * D⁻¹ ^ 2 *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by
  have hraw := transportedBad_le p S hS hM
  have hq := transportGap_pos hchi
  have hD := hS.D_pos
  have hx : 0 ≤ D * (M : ℝ) := by positivity
  have hpay := square_exp_payment hq hx
  have hexpSplit :
      Real.exp (-(r * D * M * Real.log 2)) =
        Real.exp (-(transportGap r chi * (D * M))) *
          Real.exp (-(chi * D * Real.log 2 * M)) := by
    rw [← Real.exp_add]
    congr 1
    unfold transportGap
    ring
  have hpoly :
      (M : ℝ) ^ 2 *
          Real.exp (-(transportGap r chi * (D * M))) ≤
        (4 / transportGap r chi ^ 2) * D⁻¹ ^ 2 := by
    have hDne : D ≠ 0 := ne_of_gt hD
    calc
      (M : ℝ) ^ 2 * Real.exp (-(transportGap r chi * (D * M))) =
          D⁻¹ ^ 2 *
            ((D * M) ^ 2 *
              Real.exp (-(transportGap r chi * (D * M)))) := by
        field_simp [hDne]
      _ ≤ D⁻¹ ^ 2 * (4 / transportGap r chi ^ 2) :=
        mul_le_mul_of_nonneg_left hpay (by positivity)
      _ = (4 / transportGap r chi ^ 2) * D⁻¹ ^ 2 := by ring
  rw [hexpSplit] at hraw
  calc
    _ ≤ 5 * C * (M : ℝ) ^ 2 * (2 : ℝ) ^ M *
        (Real.exp (-(transportGap r chi * (D * M))) *
          Real.exp (-(chi * D * Real.log 2 * M))) := hraw
    _ = 5 * C *
        ((M : ℝ) ^ 2 *
          Real.exp (-(transportGap r chi * (D * M)))) *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by ring
    _ ≤ 5 * C *
        ((4 / transportGap r chi ^ 2) * D⁻¹ ^ 2) *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by
      have hfiveC : 0 ≤ 5 * C := mul_nonneg (by norm_num) hS.C_pos.le
      gcongr
    _ = (20 / transportGap r chi ^ 2) * C * D⁻¹ ^ 2 *
        Real.exp (-(chi * D * Real.log 2 * M)) * (2 : ℝ) ^ M := by ring
end FirstPassageLinearTransport
