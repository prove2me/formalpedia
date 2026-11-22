-- Prove2me | solution 1 for GJKKL.Trajectory.trend_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:11:26.835246+00:00
-- url     : https://prove2.me/submissions/cc267931-22f0-44f6-a2e9-f2b273449dd8

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Trend

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
namespace GJKKL.Trajectory
theorem _root_.solution {K1 κ c B dh δ aP Asz D loss g r : ℝ} (hK1 : 0 ≤ K1) (hκ : 0 ≤ κ)
    (hc : 0 ≤ c) (hdh : 0 < dh) (hδ0 : 0 ≤ δ) (hδ : δ ≤ dh / 2) (haP : 16 ≤ aP)
    (hDL : dh - δ ≤ D) (hDU : D ≤ dh + δ) (hAL : aP * (dh - δ) ≤ Asz)
    (hAU : Asz ≤ aP * (dh + δ)) (hDA : D ≤ Asz)
    (hloss : D * K1 * (dh - δ) - D * κ * c ≤ loss) (hg0 : 0 ≤ g) (hg : g ≤ K1 * dh / aP)
    (hr : B * δ / aP ≤ r) (hB : 32 * K1 ≤ B) (hBc : 8 * κ * c ≤ B * δ) :
    -loss + (Asz - D) * (g - r) ≤ 0 := by
  have haP0 : 0 < aP := by linarith
  have hB0 : 0 ≤ B := by linarith
  have hD0 : 0 ≤ D := by linarith
  have h1 : (Asz - D) * g ≤ K1 * (dh + δ) * dh := by
    calc (Asz - D) * g ≤ Asz * g := by nlinarith
      _ ≤ aP * (dh + δ) * g := mul_le_mul_of_nonneg_right hAU hg0
      _ ≤ aP * (dh + δ) * (K1 * dh / aP) := mul_le_mul_of_nonneg_left hg (by positivity)
      _ = K1 * (dh + δ) * dh := by field_simp
  have h2 : B * δ * dh * (13 / 32) ≤ (Asz - D) * r := by
    have hAD : aP * (dh - δ) - (dh + δ) ≤ Asz - D := by linarith
    have hpos : 0 ≤ aP * (dh - δ) - (dh + δ) := by nlinarith
    have hr0 : 0 ≤ B * δ / aP := by positivity
    have hρ : (dh + δ) / aP ≤ 3 * dh / 32 := by
      rw [div_le_iff₀ haP0]; nlinarith
    calc B * δ * dh * (13 / 32) ≤ B * δ * ((dh - δ) - (dh + δ) / aP) := by
          have hx : dh * (13 / 32) ≤ (dh - δ) - (dh + δ) / aP := by linarith
          have := mul_le_mul_of_nonneg_left hx (show 0 ≤ B * δ by positivity)
          linarith
      _ = (aP * (dh - δ) - (dh + δ)) * (B * δ / aP) := by field_simp
      _ ≤ (Asz - D) * (B * δ / aP) := mul_le_mul_of_nonneg_right hAD hr0
      _ ≤ (Asz - D) * r := mul_le_mul_of_nonneg_left hr (by linarith)
  have h3 : (dh - δ) * K1 * (dh - δ) - (dh + δ) * κ * c ≤ loss := by
    have ha : (dh - δ) * (K1 * (dh - δ)) ≤ D * (K1 * (dh - δ)) :=
      mul_le_mul_of_nonneg_right hDL (by nlinarith)
    have hb : D * (κ * c) ≤ (dh + δ) * (κ * c) := mul_le_mul_of_nonneg_right hDU (by positivity)
    nlinarith
  have h4 : K1 * (dh + δ) * dh - (dh - δ) * K1 * (dh - δ) ≤ B * δ * dh * (3 / 32) := by
    have : K1 * (dh + δ) * dh - (dh - δ) * K1 * (dh - δ) = K1 * (3 * dh * δ - δ ^ 2) := by ring
    rw [this]
    have hδdh : 0 ≤ δ * dh := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hB hδdh, sq_nonneg δ, mul_nonneg hK1 (sq_nonneg δ)]
  have h5 : (dh + δ) * κ * c ≤ B * δ * dh * (6 / 32) := by
    have hκc : 0 ≤ κ * c := by positivity
    have : (dh + δ) * (κ * c) ≤ (3 / 2 * dh) * (κ * c) := mul_le_mul_of_nonneg_right (by linarith) hκc
    nlinarith
  have hBδdh : 0 ≤ B * δ * dh := by positivity
  have e : -loss + (Asz - D) * (g - r) = -loss + (Asz - D) * g - (Asz - D) * r := by ring
  rw [e]
  linarith
end GJKKL.Trajectory
