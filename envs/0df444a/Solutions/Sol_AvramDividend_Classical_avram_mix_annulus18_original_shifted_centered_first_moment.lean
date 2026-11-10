-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_annulus18_original_shifted_centered_first_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:37:50.877475+00:00
-- url     : https://prove2.me/submissions/cb557df9-12f1-48f6-9677-07478e0d54d5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus16_original_zero_origin_centered_mean
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0)
    (n m : ℕ) (hnm : n ≤ m) :
    let B : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B)
    let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
    Integrable (fun ω => (N ω).toReal - r) P ∧
      (∫ ω, (N ω).toReal - r ∂P) = 0 := by
  dsimp only
  let B : Set ℝ :=
    Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let r : ℝ := ((T : ℝ≥0∞) * X.ν B).toReal
  have hB : MeasurableSet B := by
    dsimp [B]
    exact measurableSet_Ioc
  have hBand : B ⊆ Iic (-(1 / ((m : ℝ) + 1))) := by
    intro z hz
    exact hz.2
  have hMem :=
    avram_p4_s3_original_negative_borel_cell_centred_L2_from_full_band
      X T m 0 T (show (0 : ℝ≥0) ≤ T from zero_le) (le_refl T) B hB hBand
  have hI : Integrable
      (fun ω => (NX ω (Ioc 0 T ×ˢ B)).toReal - r) P := by
    simpa [NX, B, r] using hMem.integrable (by norm_num)
  have hstat :=
    avram_p4_s3_interval_h_original_intrinsic_marked_real_moment_stationary
      X NX (by intro ω; rfl) s T B hB
      (fun z : ℝ≥0∞ => z.toReal - r) (by fun_prop) hI
  have hmean :=
    avram_mix_annulus16_original_zero_origin_centered_mean X T n m hnm
  constructor
  · simpa [NX, B, r] using hstat.1
  · calc
      (∫ ω, (NX ω (Ioc s (s + T) ×ˢ B)).toReal - r ∂P)
          = ∫ ω, (NX ω (Ioc 0 T ×ˢ B)).toReal - r ∂P :=
              hstat.2
      _ = 0 := by simpa [NX, B, r] using hmean
