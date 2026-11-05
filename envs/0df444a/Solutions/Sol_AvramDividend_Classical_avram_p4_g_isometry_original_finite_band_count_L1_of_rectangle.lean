-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_finite_band_count_L1_of_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:19:30.976141+00:00
-- url     : https://prove2.me/submissions/cecfa268-c42a-4452-a2c5-9337f1a9868a

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Original intrinsic finite-band count is integrable and finite almost everywhere. -/
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
    (hMeas : Measurable N)
    (hRect : ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      (∫⁻ ω in A, N ω ∂P) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    Integrable (fun ω => (N ω).toReal) P ∧
      (∀ᵐ ω ∂P, N ω < ⊤) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hAll : (∫⁻ ω, N ω ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    simpa using hRect Set.univ
      (show MeasurableSet[𝓕 s] (Set.univ : Set Ω) from MeasurableSet.univ)
  have hFinite : (∫⁻ ω, N ω ∂P) ≠ ⊤ := by
    rw [hAll]
    exact ne_of_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hν)
  exact ⟨integrable_toReal_of_lintegral_ne_top
    hMeas.aemeasurable hFinite, ae_lt_top hMeas hFinite⟩
