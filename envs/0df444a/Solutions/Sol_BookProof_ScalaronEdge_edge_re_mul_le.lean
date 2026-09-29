-- Prove2me | solution 1 for BookProof.ScalaronEdge.edge_re_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:42:37.359017+00:00
-- url     : https://prove2.me/submissions/1dc24a31-acd9-444c-9f8d-63e2a23c1040

-- Generated from ChapterScalaronEdge.lean — solution of BookProof.ScalaronEdge.edge_re_mul_le
import Mathlib
import Definitions.Def_ChapterScalaronEdge
open BookProof.ScalaronEdge










open Complex Real MeasureTheory Function SchwartzMap ComplexOrder
open BookProof.Starobinsky
open BookProof.ScalaronWallEsa
open BookProof.ScalaronEsa
open BookProof.FarisLavine
open BookProof.WallEsaSemibounded
open BookProof.FriedrichsExtension
open BookProof.FriedrichsFormGap
open BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert



variable (M alpha : ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (z w : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ((starRingEnd ℂ) w * z + (starRingEnd ℂ) z * w).re ≤ δ * ‖z‖ ^ 2 + δ⁻¹ * ‖w‖ ^ 2 := by

  have h1 : ((starRingEnd ℂ) w * z + (starRingEnd ℂ) z * w).re
      ≤ ‖(starRingEnd ℂ) w * z + (starRingEnd ℂ) z * w‖ := Complex.re_le_norm _
  have h2 : ‖(starRingEnd ℂ) w * z + (starRingEnd ℂ) z * w‖ ≤ 2 * (‖z‖ * ‖w‖) := by
    calc ‖(starRingEnd ℂ) w * z + (starRingEnd ℂ) z * w‖
        ≤ ‖(starRingEnd ℂ) w * z‖ + ‖(starRingEnd ℂ) z * w‖ := norm_add_le _ _
      _ = 2 * (‖z‖ * ‖w‖) := by simp [mul_comm]; ring
  have h3 : δ * ‖z‖ ^ 2 + δ⁻¹ * ‖w‖ ^ 2 - 2 * (‖z‖ * ‖w‖) = δ⁻¹ * (δ * ‖z‖ - ‖w‖) ^ 2 := by
    field_simp; ring
  nlinarith [sq_nonneg (δ * ‖z‖ - ‖w‖), inv_pos.mpr hδ]
