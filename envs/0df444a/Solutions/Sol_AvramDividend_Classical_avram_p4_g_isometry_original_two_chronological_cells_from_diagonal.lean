-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_two_chronological_cells_from_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:59:39.717126+00:00
-- url     : https://prove2.me/submissions/53ba5884-0e84-4c3c-bf40-a7bdfdbb7bbb

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_past_cross_zero_from_proved_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_diagonal_of_source_second_rectangle

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Physical two consecutive marked-band compensated blocks satisfy the predictable L² isometry when their source conditional diagonals hold. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (s u t : ℝ≥0) (hsu : s ≤ u) (hut : u ≤ t) (ε : ℝ) (hε : 0 < ε) (B₁ B₂ : Set ℝ) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂) (hBand₁ : B₁ ⊆ Ioo (-1 : ℝ) (-ε)) (hBand₂ : B₂ ⊆ Ioo (-1 : ℝ) (-ε)) (hν₁ : X.ν B₁ < ⊤) (hν₂ : X.ν B₂ < ⊤) (N₁ N₂ : Ω → ℝ≥0∞) (hActual₁ : N₁ = fun ω => ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map (fun v : ℝ≥0 => (v, X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc s u ×ˢ B₁)) (hActual₂ : N₂ = fun ω => ((Measure.count.restrict {v : ℝ≥0 | 0 < v ∧ X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map (fun v : ℝ≥0 => (v, X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc u t ×ˢ B₂)) (hMeas₂ : Measurable N₂) (r₁ r₂ : ℝ) (hRate₁ : r₁ = (((u - s : ℝ≥0) : ℝ≥0∞) * X.ν B₁).toReal) (hRate₂ : r₂ = (((t - u : ℝ≥0) : ℝ≥0∞) * X.ν B₂).toReal) (H₁ H₂ : Ω → ℝ) (hH₁ : StronglyMeasurable[𝓕 s] H₁) (hH₂ : StronglyMeasurable[𝓕 u] H₂) (hPast₁ : StronglyMeasurable[𝓕 u] (fun ω => H₁ ω * ((N₁ ω).toReal - r₁))) (hPairL2 : MemLp (fun ω => (H₁ ω * ((N₁ ω).toReal - r₁)) * H₂ ω) 2 P) (hCount₂L2 : MemLp (fun ω => (N₂ ω).toReal - r₂) 2 P) (hSecond₁ : P[(fun ω => ((N₁ ω).toReal - r₁) ^ 2) | 𝓕 s] =ᵐ[P] (fun _ => r₁)) (hSecond₂ : P[(fun ω => ((N₂ ω).toReal - r₂) ^ 2) | 𝓕 u] =ᵐ[P] (fun _ => r₂)) (hSq₁ : Integrable (fun ω => ((N₁ ω).toReal - r₁) ^ 2) P) (hSq₂ : Integrable (fun ω => ((N₂ ω).toReal - r₂) ^ 2) P) (hHSq₁ : Integrable (fun ω => (H₁ ω) ^ 2) P) (hHSq₂ : Integrable (fun ω => (H₂ ω) ^ 2) P) (hWSq₁ : Integrable (fun ω => (H₁ ω) ^ 2 * ((N₁ ω).toReal - r₁) ^ 2) P) (hWSq₂ : Integrable (fun ω => (H₂ ω) ^ 2 * ((N₂ ω).toReal - r₂) ^ 2) P) : (∫ ω, (H₁ ω * ((N₁ ω).toReal - r₁) + H₂ ω * ((N₂ ω).toReal - r₂)) ^ 2 ∂P) = r₁ * ∫ ω, (H₁ ω) ^ 2 ∂P + r₂ * ∫ ω, (H₂ ω) ^ 2 ∂P := by
  letI : MeasurableSpace Ω := mΩ
  let D₁ : Ω → ℝ := fun ω => H₁ ω * ((N₁ ω).toReal - r₁)
  let D₂ : Ω → ℝ := fun ω => H₂ ω * ((N₂ ω).toReal - r₂)
  have hCrossInt : Integrable (fun ω => D₁ ω * D₂ ω) P := by
    have hi := hPairL2.integrable_mul hCount₂L2
    convert hi using 1
    funext ω
    simp only [Pi.mul_apply, D₁, D₂]
    ring
  have hCross : (∫ ω, D₁ ω * D₂ ω ∂P) = 0 := by
    have hPair : MemLp (fun ω => D₁ ω * H₂ ω) 2 P := by
      simpa only [D₁] using hPairL2
    have hz := avram_p4_g_isometry_original_past_cross_zero_from_proved_compensator
      X u t hut ε hε B₂ hB₂ hBand₂ hν₂ N₂ hActual₂ hMeas₂
      D₁ H₂ hPast₁ hH₂ hPair
      (by simpa only [hRate₂] using hCount₂L2)
    simpa only [D₂, hRate₂] using hz
  have hDiag₁ := avram_p4_g_isometry_original_raw_diagonal_of_source_second_rectangle
    X s u hsu ε hε B₁ hB₁ hBand₁ hν₁ N₁ hActual₁
    r₁ hRate₁ hSecond₁ H₁ hH₁ hSq₁ hHSq₁ hWSq₁
  have hDiag₂ := avram_p4_g_isometry_original_raw_diagonal_of_source_second_rectangle
    X u t hut ε hε B₂ hB₂ hBand₂ hν₂ N₂ hActual₂
    r₂ hRate₂ hSecond₂ H₂ hH₂ hSq₂ hHSq₂ hWSq₂
  have hD₁Sq : Integrable (fun ω => (D₁ ω) ^ 2) P := by
    simpa only [D₁, mul_pow] using hWSq₁
  have hD₂Sq : Integrable (fun ω => (D₂ ω) ^ 2) P := by
    simpa only [D₂, mul_pow] using hWSq₂
  change (∫ ω, (D₁ ω + D₂ ω) ^ 2 ∂P) =
    r₁ * ∫ ω, (H₁ ω) ^ 2 ∂P +
      r₂ * ∫ ω, (H₂ ω) ^ 2 ∂P
  calc
    (∫ ω, (D₁ ω + D₂ ω) ^ 2 ∂P) =
        ∫ ω, ((D₁ ω) ^ 2 + 2 * (D₁ ω * D₂ ω) +
          (D₂ ω) ^ 2) ∂P := by
      congr 1
      funext ω
      ring
    _ = (∫ ω, (D₁ ω) ^ 2 ∂P) +
        2 * (∫ ω, D₁ ω * D₂ ω ∂P) +
        (∫ ω, (D₂ ω) ^ 2 ∂P) := by
      calc
        (∫ ω, ((D₁ ω)^2 + 2 * (D₁ ω * D₂ ω) + (D₂ ω)^2) ∂P) =
            (∫ ω, ((D₁ ω)^2 + 2 * (D₁ ω * D₂ ω)) ∂P) +
              (∫ ω, (D₂ ω)^2 ∂P) := by
                exact integral_add (hD₁Sq.add (hCrossInt.const_mul 2)) hD₂Sq
        _ = ((∫ ω, (D₁ ω)^2 ∂P) +
              (∫ ω, 2 * (D₁ ω * D₂ ω) ∂P)) +
              (∫ ω, (D₂ ω)^2 ∂P) := by
                congr 1
                exact integral_add hD₁Sq (hCrossInt.const_mul 2)
        _ = (∫ ω, (D₁ ω)^2 ∂P) +
              2 * (∫ ω, D₁ ω * D₂ ω ∂P) +
              (∫ ω, (D₂ ω)^2 ∂P) := by
                congr 2
                simp only [integral_const_mul]
    _ = r₁ * ∫ ω, (H₁ ω) ^ 2 ∂P +
        r₂ * ∫ ω, (H₂ ω) ^ 2 ∂P := by
      rw [hCross]
      simp only [mul_zero, add_zero]
      simpa only [D₁, D₂] using congrArg₂ (· + ·) hDiag₁ hDiag₂
