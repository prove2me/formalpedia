-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_physical_weighted_condExp_zero_meas_and_rate_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:20:49.41872+00:00
-- url     : https://prove2.me/submissions/b36455dd-3379-4079-ab41-9e1bf8fd1075

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_intrinsic_general_time_mark_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_weighted_finite_band_condExp_zero_no_rectangle

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical finite-band centred counts need no assumed measurability or rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (N : Ω → ℝ≥0∞)
    (hActual : N = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P)
    (hCountL2 : MemLp (fun ω => (N ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) 2 P) :
    P[(fun ω => H ω * ((N ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) | 𝓕 s] =ᵐ[P] 0 := by
  have hSep : B ⊆ Iic (-ε) := by
    intro z hz
    exact (hBand hz).2.le
  have hν : X.ν B < ⊤ :=
    avram_p2_a_zero_rate_separated_borel_nu_finite X B hB ε hε hSep
  have hMeas : Measurable N := by
    rw [hActual]
    exact avram_p2_d_future_intrinsic_general_time_mark_measurable X
      (Ioc s t ×ˢ B) (measurableSet_Ioc.prod hB)
  exact avram_p4_s3_original_weighted_finite_band_condExp_zero_no_rectangle
    X s t hst ε hε B hB hBand hν N hActual hMeas H hH hHL2 hCountL2
