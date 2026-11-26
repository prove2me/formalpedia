-- Prove2me | solution 1 for CondMat0408017.rms_height_difference_topothesy
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:21:58.741017+00:00
-- url     : https://prove2.me/submissions/b0553ab4-c585-4639-bcb6-a97bbf2aa436

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex CondMat0408017

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ζ : ℝ → Ω → ℝ) (H ξm ξp ℓ : ℝ) (hξm : 0 ≤ ξm)
    (hstat : ∀ x Δ : ℝ,
      ProbabilityTheory.IdentDistrib (fun w => ζ (x + Δ) w - ζ x w) (fun w => ζ Δ w - ζ 0 w) P P)
    (hsa : ∀ Δ l : ℝ, 0 < l → Δ ∈ Set.Ioo ξm ξp → l * Δ ∈ Set.Ioo ξm ξp →
      ProbabilityTheory.IdentDistrib (fun w => ζ Δ w - ζ 0 w) (fun w => l ^ (-H) * (ζ (l * Δ) w - ζ 0 w)) P P)
    (hℓ : ℓ ∈ Set.Ioo ξm ξp) (h37 : rmsHeightDiff P ζ ℓ = ℓ) :
    ∀ x Δ : ℝ, Δ ∈ Set.Ioo ξm ξp →
      Real.sqrt (∫ w, (ζ (x + Δ) w - ζ x w) ^ 2 ∂P) = ℓ ^ (1 - H) * Δ ^ H := by
  intro x Δ hΔ
  have hΔ_pos : 0 < Δ := lt_of_le_of_lt hξm hΔ.1
  have hℓ_pos : 0 < ℓ := lt_of_le_of_lt hξm hℓ.1
  have hl_pos : 0 < ℓ / Δ := div_pos hℓ_pos hΔ_pos
  have hlΔ : (ℓ / Δ) * Δ = ℓ := div_mul_cancel₀ ℓ hΔ_pos.ne'
  have h1 : ∫ w, (ζ (x + Δ) w - ζ x w) ^ 2 ∂P = ∫ w, (ζ Δ w - ζ 0 w) ^ 2 ∂P :=
    ((hstat x Δ).comp (measurable_id.pow_const 2)).integral_eq
  have h2 : ∫ w, (ζ Δ w - ζ 0 w) ^ 2 ∂P =
      ∫ w, ((ℓ / Δ) ^ (-H) * (ζ ((ℓ / Δ) * Δ) w - ζ 0 w)) ^ 2 ∂P :=
    ((hsa Δ (ℓ / Δ) hl_pos hΔ (by rwa [hlΔ])).comp (measurable_id.pow_const 2)).integral_eq
  rw [h1, h2, hlΔ]
  have h3 : (fun w => ((ℓ / Δ) ^ (-H) * (ζ ℓ w - ζ 0 w)) ^ 2) =
      fun w => ((ℓ / Δ) ^ (-H)) ^ 2 * (ζ ℓ w - ζ 0 w) ^ 2 := by
    ext w; ring
  rw [h3, integral_const_mul, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (Real.rpow_pos_of_pos hl_pos (-H)).le]
  change (ℓ / Δ) ^ (-H) * rmsHeightDiff P ζ ℓ = ℓ ^ (1 - H) * Δ ^ H
  rw [h37, Real.div_rpow hℓ_pos.le hΔ_pos.le, Real.rpow_neg hℓ_pos.le, Real.rpow_neg hΔ_pos.le,
    Real.rpow_sub hℓ_pos, Real.rpow_one]
  field_simp [(Real.rpow_pos_of_pos hℓ_pos H).ne', (Real.rpow_pos_of_pos hΔ_pos H).ne']
