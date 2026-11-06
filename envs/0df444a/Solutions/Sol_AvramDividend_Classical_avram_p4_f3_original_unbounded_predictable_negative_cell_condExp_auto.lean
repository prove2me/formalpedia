-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_unbounded_predictable_negative_cell_condExp_auto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:46:08.395158+00:00
-- url     : https://prove2.me/submissions/1db4536d-ba75-4609-8e9e-4044235a16c8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_separated_borel_nu_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_weighted_finite_band_condExp_zero_no_rectangle
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Unbounded L²-predictable weights preserve the true physical jump-cell conditional mean zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (n : ℕ)
    (s t : ℝ≥0) (hst : s ≤ t) (htT : t ≤ T)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hCut : B ⊆ Iic (-(1 / ((n : ℝ) + 1))))
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hHL2 : MemLp H 2 P) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)
    let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
    P[(fun ω => H ω * ((N ω).toReal - r)) | 𝓕 s] =ᵐ[P] 0 := by
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B)
  let r : ℝ := (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal
  change P[(fun ω => H ω * ((N ω).toReal - r)) | 𝓕 s] =ᵐ[P] 0
  have hBsep : B ⊆ Iic (-ε) := by
    intro z hz
    exact le_of_lt (hBand hz).2
  have hν : X.ν B < ⊤ :=
    avram_p2_a_zero_rate_separated_borel_nu_finite
      X B hB ε hε hBsep
  have hNm : Measurable N :=
    avram_p2_e_compensator_original_intrinsic_marked_count_measurable
      X s t hst B hB
  have hNL2 : MemLp (fun ω => (N ω).toReal - r) 2 P :=
    avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
      X T n s t hst htT B hB hCut
  exact avram_p4_s3_original_weighted_finite_band_condExp_zero_no_rectangle
    X s t hst ε hε B hB hBand hν N rfl hNm H hH hHL2 hNL2
