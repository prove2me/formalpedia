-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_weighted_finite_band_condExp_zero_no_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:12:29.259041+00:00
-- url     : https://prove2.me/submissions/54162112-f3e8-4c7d-8609-d46699431ef3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_future_negative_borel_rectangle_all_cells
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_weighted_condExp_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Centred physical finite-band increments have zero weighted past conditional mean. -/
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
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P)
    (hCountL2 : MemLp (fun ω => (N ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) 2 P) :
    P[(fun ω => H ω * ((N ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) | 𝓕 s] =ᵐ[P] 0 := by
  have hSep : B ⊆ Iic (-ε) := by
    intro z hz
    exact (hBand hz).2.le
  have hRect : ∀ A : Set Ω, MeasurableSet[𝓕 s] A →
      (∫⁻ ω in A, N ω ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
    intro A hA
    rw [hActual]
    exact avram_p4_s3_original_future_negative_borel_rectangle_all_cells
      X B hB ε hε hSep s t hst A hA
  exact avram_p4_g_isometry_original_raw_weighted_condExp_zero
    X s t hst ε hε B hB hBand hν
    N hActual hMeas hRect H hH hHL2 hCountL2
