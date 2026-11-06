-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_marked_borel_cell_centered_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:08:14.509196+00:00
-- url     : https://prove2.me/submissions/9847fe22-bbf8-4c21-9fc0-4c5ef41c4332

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_future_negative_borel_rectangle_all_cells
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A separated original marked cell has its exact compensator mean. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε))
    (A : Ω → ℝ)
    (hAeq : ∀ ω, A ω =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)
    (hNfinite : ∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) < ⊤)
    (hAi : Integrable A P) :
    let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => A ω - r) P ∧
      (∫ ω, A ω - r ∂P) = 0 := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B)
  let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
  change Integrable (fun ω => A ω - r) P ∧
    (∫ ω, A ω - r ∂P) = 0
  have hOfReal (ω : Ω) : ENNReal.ofReal (A ω) = N ω := by
    rw [hAeq ω]
    exact ENNReal.ofReal_toReal (ne_of_lt (hNfinite ω))
  have hPos (ω : Ω) : 0 ≤ A ω := by
    rw [hAeq ω]
    exact ENNReal.toReal_nonneg
  have hRate := avram_p4_s3_original_future_negative_borel_rectangle_all_cells
    X B hB ε hε hBsep s t hst Set.univ
    (by simp)
  have hLin : (∫⁻ ω, ENNReal.ofReal (A ω) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    calc
      _ = ∫⁻ ω, N ω ∂P :=
        lintegral_congr (fun ω => hOfReal ω)
      _ = ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
        simpa only [Measure.restrict_univ, measure_univ, one_mul] using hRate
  have hReal := ofReal_integral_eq_lintegral_ofReal
    hAi (Filter.Eventually.of_forall hPos)
  have hMeanNonneg : 0 ≤ ∫ ω, A ω ∂P :=
    integral_nonneg hPos
  have hMean : (∫ ω, A ω ∂P) = r := by
    have hEq : ENNReal.ofReal (∫ ω, A ω ∂P) =
        ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
      exact hReal.trans hLin
    have := congrArg ENNReal.toReal hEq
    simpa only [ENNReal.toReal_ofReal hMeanNonneg] using this
  refine ⟨hAi.sub (integrable_const r), ?_⟩
  simp only [integral_sub hAi (integrable_const r), integral_const,
    smul_eq_mul, measure_univ, one_mul, hMean, sub_self]
  simp [Measure.real]
