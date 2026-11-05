-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_physical_band_centred_count_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T21:49:05.938089+00:00
-- url     : https://prove2.me/submissions/89f5d704-5484-49c9-80d0-1bb170badb43

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_band_L1_mean_auto_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_factorial_from_physical_pair_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_centered_count_L2_of_factorial_integrability

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Original physical marked-band centred counts have finite L2 energy. -/
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
    MemLp (fun ω => (N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) 2 P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hMean :
      Integrable (fun ω => (N ω).toReal) P :=
    (avram_p4_g_isometry_original_band_L1_mean_auto_compensator
      X s t hst ε hε B hB hBand hν N hActual).1
  have hFactorial :
      Integrable (fun ω => (N ω).toReal *
        ((N ω).toReal - 1)) P :=
    (avram_p4_g_isometry_original_factorial_from_physical_pair_lintegral
      X s t hst ε hε B hB hBand hν N hActual K hKMeas
      hPhysicalPair hPairMean).1
  exact avram_p4_g_isometry_centered_count_L2_of_factorial_integrability
    (fun ω => (N ω).toReal)
    ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)
    hMean hFactorial
