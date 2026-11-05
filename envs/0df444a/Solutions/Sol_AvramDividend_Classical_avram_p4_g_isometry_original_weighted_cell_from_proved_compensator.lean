-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_weighted_cell_from_proved_compensator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:29:46.170354+00:00
-- url     : https://prove2.me/submissions/c65475cd-f041-4282-9600-59ac45c76224

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_weighted_martingale_step

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Physical finite-band predictable weighted increment, using the proved original rectangle compensator. -/
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
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P)
    (hCountL2 : MemLp (fun ω => (N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) 2 P)
    (M : Ω → ℝ)
    (hM : StronglyMeasurable[𝓕 s] M)
    (hMInt : Integrable M P) :
    P[(fun ω => M ω + H ω * ((N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) | 𝓕 s]
        =ᵐ[P] M := by
  have hRect : ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      (∫⁻ ω in A, N ω ∂P) =
        P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    intro A hA
    simpa only [hActual] using
      (avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
        X s t hst A hA B hB)
  exact avram_p4_g_isometry_original_raw_weighted_martingale_step
    X s t hst ε hε B hB hBand hν N hActual hMeas hRect
    H hH hHL2 hCountL2 M hM hMInt
