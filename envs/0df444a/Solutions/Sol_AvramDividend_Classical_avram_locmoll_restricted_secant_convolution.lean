-- Prove2me | solution 1 for AvramDividend.Classical.avram_locmoll_restricted_secant_convolution
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T19:01:33.359538+00:00
-- url     : https://prove2.me/submissions/2fc905a0-0ce0-47b3-a1e4-390ef325e4d4

import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem solution
    (μ : Measure ℝ) (ρ w : ℝ → ℝ)
    (ε a b c : ℝ) (hε : 0 < ε)
    (ha : 2 * ε ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (hρI : Integrable ρ μ)
    (hρnorm : (∫ r, ρ r ∂μ) = 1)
    (hρpos : 0 ≤ᵐ[μ] ρ)
    (hρsupport : ∀ᵐ r ∂μ, ρ r ≠ 0 → r ∈ Icc ε (2 * ε))
    (hsec : ∀ u v : ℝ, 0 ≤ u → u ≤ v → v ≤ c →
      v - u ≤ w v - w u)
    (haI : Integrable (fun r => ρ r * w (a - r)) μ)
    (hbI : Integrable (fun r => ρ r * w (b - r)) μ) :
    b - a ≤ (∫ r, ρ r * w (b - r) ∂μ) -
      (∫ r, ρ r * w (a - r) ∂μ) := by
  have hp : ∀ᵐ r ∂μ,
      ρ r * (b - a) ≤ ρ r * w (b - r) - ρ r * w (a - r) := by
    filter_upwards [hρpos, hρsupport] with r hr hsupport
    by_cases hz : ρ r = 0
    · simp [hz]
    · have hmem := hsupport hz
      have hu : 0 ≤ a - r := by linarith [hmem.2]
      have huv : a - r ≤ b - r := by linarith
      have hv : b - r ≤ c := by linarith [hmem.1]
      have hs := hsec (a - r) (b - r) hu huv hv
      have ht : b - a ≤ w (b - r) - w (a - r) := by linarith
      simpa [mul_sub] using mul_le_mul_of_nonneg_left ht hr
  have hh := integral_mono_ae (hρI.mul_const (b - a))
    (hbI.sub haI) hp
  change (∫ r, ρ r * (b - a) ∂μ) ≤
    ∫ r, ρ r * w (b - r) - ρ r * w (a - r) ∂μ at hh
  rw [integral_sub hbI haI, integral_mul_const, hρnorm, one_mul] at hh
  exact hh
