-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_factorial_from_physical_pair_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T19:01:30.135022+00:00
-- url     : https://prove2.me/submissions/fd3db6e0-30b6-4eae-8161-20ab145f6353

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original physical ordered-pair intensity yields factorial integrability and second moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : X.ν B < ⊤)
    (N : Ω → ℝ≥0∞)
    (hActual : N = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (K : Ω → ℝ≥0∞) (hKMeas : Measurable K)
    (hPhysicalPair : ∀ ω,
      (N ω).toReal * ((N ω).toReal - 1) = 2 * (K ω).toReal)
    (hPairMean :
      (∫⁻ ω, K ω ∂P) = ENNReal.ofReal
        (((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) ^ 2 / 2)) :
    Integrable (fun ω =>
      (N ω).toReal * ((N ω).toReal - 1)) P ∧
    (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) =
      ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) ^ 2 := by
  let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
  have hKfinite : (∫⁻ ω, K ω ∂P) ≠ ⊤ := by
    rw [hPairMean]
    exact ENNReal.ofReal_ne_top
  have hKaefinite : ∀ᵐ ω ∂P, K ω < ⊤ :=
    ae_lt_top hKMeas hKfinite
  have hKInt : Integrable (fun ω => (K ω).toReal) P :=
    integrable_toReal_of_lintegral_ne_top hKMeas.aemeasurable hKfinite
  have hKReal : (∫ ω, (K ω).toReal ∂P) = r ^ 2 / 2 := by
    rw [integral_toReal hKMeas.aemeasurable hKaefinite]
    rw [hPairMean]
    exact ENNReal.toReal_ofReal (div_nonneg (sq_nonneg _) (by norm_num))
  have hPathwise : (fun ω => (N ω).toReal *
      ((N ω).toReal - 1)) = fun ω => 2 * (K ω).toReal := by
    funext ω
    exact hPhysicalPair ω
  rw [hPathwise]
  constructor
  · exact hKInt.const_mul 2
  · rw [integral_const_mul, hKReal]
    dsimp [r]
    ring
