-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_raw_past_event_centred_finite_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:25:47.080486+00:00
-- url     : https://prove2.me/submissions/ef1ad92f-6d74-4ea6-9224-129c6ab2257c

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Actual intrinsic compensated finite-band count has zero mean on raw past events. -/
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
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫ ω in A,
      ((N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) ∂P) = 0 := by
  letI : IsProbabilityMeasure P := X.isProbability
  let r : ℝ≥0∞ := ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B
  have hr : r < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hν
  have hp : P A < ⊤ := measure_lt_top P A
  have hE : (∫⁻ ω in A, N ω ∂P) = P A * r := by
    simpa only [r, mul_assoc] using hRect A hA
  have hfin : (∫⁻ ω in A, N ω ∂P) ≠ ⊤ := by
    rw [hE]
    exact (ENNReal.mul_lt_top hp hr).ne
  have hAE : ∀ᵐ ω ∂(P.restrict A), N ω < ⊤ :=
    ae_lt_top hMeas hfin
  have hInt : Integrable (fun ω => (N ω).toReal) (P.restrict A) :=
    integrable_toReal_of_lintegral_ne_top hMeas.aemeasurable hfin
  have hReal : (∫ ω in A, (N ω).toReal ∂P) =
      (P A * r).toReal := by
    rw [integral_toReal hMeas.aemeasurable hAE]
    exact congrArg ENNReal.toReal hE
  change (∫ ω in A, (N ω).toReal - r.toReal ∂P) = 0
  rw [integral_sub hInt (integrable_const r.toReal)]
  rw [hReal]
  simp only [integral_const, smul_eq_mul]
  have hmass : (P.restrict A).real Set.univ = (P A).toReal := by
    simp [Measure.real]
  rw [hmass, ENNReal.toReal_mul]
  ring
