-- Prove2me | solution 1 for GJKKL.Trajectory.trend_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:12:40.69751+00:00
-- url     : https://prove2.me/submissions/684e63ba-180f-4876-b369-e3269cb37201

module
public import Mathlib
public import Definitions.Def_GJKKL_Trajectory_Trend

set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Trajectory
namespace GJKKL.Trajectory
theorem _root_.solution {K1 K2 B dh δ aP Asz D loss g r : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hdh : 0 < dh) (hδ0 : 0 ≤ δ) (hδ : δ ≤ dh / 2) (haP : 16 ≤ aP) (haPK2 : K2 ≤ aP)
    (hDU : D ≤ dh + δ) (hAL : aP * (dh - δ) ≤ Asz) (hD0 : 0 ≤ D)
    (hloss : loss ≤ D * K1 * (dh + δ)) (hg : K1 * dh / aP - K1 * K2 * dh / aP ^ 2 ≤ g)
    (hr : B * δ / aP ≤ r) (hB : 32 * K1 ≤ B) (hBn : 4 * K1 * (2 + K2) * dh ≤ B * δ * aP) :
    loss - (Asz - D) * (g + r) ≤ 0 := by
  have haP0 : 0 < aP := by linarith
  have hB0 : 0 ≤ B := by linarith
  set ρ := (dh + δ) / aP with hρdef
  have hρ : ρ ≤ 3 * dh / 32 := by rw [hρdef, div_le_iff₀ haP0]; nlinarith
  have hρ0 : 0 ≤ ρ := by positivity
  have hAD : aP * (dh - δ) - (dh + δ) ≤ Asz - D := by linarith
  have hpos : 0 ≤ aP * (dh - δ) - (dh + δ) := by nlinarith
  -- the lower bound for `g + r`, put over the common denominator `aP`
  set Q := K1 * dh * (1 - K2 / aP) + B * δ with hQdef
  have hK2aP : 0 ≤ 1 - K2 / aP := by rw [sub_nonneg, div_le_one haP0]; exact haPK2
  have hQ0 : 0 ≤ Q := by positivity
  have hgr : Q / aP ≤ g + r := by
    have : Q / aP = K1 * dh / aP - K1 * K2 * dh / aP ^ 2 + B * δ / aP := by
      rw [hQdef]; field_simp
    rw [this]; linarith
  have hmain : (dh - δ - ρ) * Q ≤ (Asz - D) * (g + r) := by
    calc (dh - δ - ρ) * Q = (aP * (dh - δ) - (dh + δ)) * (Q / aP) := by
          rw [hρdef]; field_simp
      _ ≤ (Asz - D) * (Q / aP) := mul_le_mul_of_nonneg_right hAD (by positivity)
      _ ≤ (Asz - D) * (g + r) := mul_le_mul_of_nonneg_left hgr (by linarith)
  have hloss' : loss ≤ K1 * (dh + δ) ^ 2 := by
    calc loss ≤ D * K1 * (dh + δ) := hloss
      _ ≤ (dh + δ) * K1 * (dh + δ) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hDU hK1
      _ = K1 * (dh + δ) ^ 2 := by ring
  -- `K1 (dh+δ)² ≤ (dh - δ - ρ) Q`
  have hdhaP : K1 * (2 + K2) * dh * (dh / aP) ≤ B * δ * dh / 4 := by
    have : K1 * (2 + K2) * dh * (dh / aP) = (K1 * (2 + K2) * dh) * dh / aP := by ring
    rw [this, div_le_iff₀ haP0]
    nlinarith [mul_le_mul_of_nonneg_right hBn hdh.le]
  have hexp : (dh - δ - ρ) * Q = K1 * dh * (dh - δ - ρ) - K1 * dh * (dh - δ - ρ) * (K2 / aP) +
      B * δ * (dh - δ - ρ) := by rw [hQdef]; ring
  have hKa : K1 * dh * (dh - δ - ρ) * (K2 / aP) ≤ K1 * K2 * dh * (dh / aP) := by
    have h1 : dh - δ - ρ ≤ dh := by linarith
    have : K1 * dh * (dh - δ - ρ) * (K2 / aP) = (K1 * dh * (K2 / aP)) * (dh - δ - ρ) := by ring
    rw [this]
    calc (K1 * dh * (K2 / aP)) * (dh - δ - ρ) ≤ (K1 * dh * (K2 / aP)) * dh :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = K1 * K2 * dh * (dh / aP) := by ring
  have hρdh : K1 * dh * ρ ≤ K1 * dh * ((3 / 2) * (dh / aP)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hρdef]
    rw [show (3 / 2) * (dh / aP) = (3 / 2 * dh) / aP by ring]
    exact div_le_div_of_nonneg_right (by linarith) haP0.le
  have hBδ : B * δ * dh * (13 / 32) ≤ B * δ * (dh - δ - ρ) := by
    have hx : dh * (13 / 32) ≤ dh - δ - ρ := by linarith
    have := mul_le_mul_of_nonneg_left hx (show 0 ≤ B * δ by positivity)
    linarith
  have hδ2 : K1 * δ ^ 2 ≤ K1 * (δ * dh / 2) := by
    apply mul_le_mul_of_nonneg_left _ hK1
    nlinarith
  have hK1B : K1 * (δ * dh) ≤ B / 32 * (δ * dh) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hdhaP0 : 0 ≤ K1 * dh * (dh / aP) := by positivity
  have hK2' : K1 * K2 * dh * (dh / aP) + K1 * dh * ((3 / 2) * (dh / aP)) ≤
      K1 * (2 + K2) * dh * (dh / aP) := by linarith
  have hBδdh : 0 ≤ B * δ * dh := by positivity
  linarith
end GJKKL.Trajectory
