-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_largejump_sum_signed_mean_triplet
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T03:47:15.720708+00:00
-- url     : https://prove2.me/submissions/255c17ed-2b2b-40db-80e6-a1802a3a598e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18q1_original_largejump_Campbell_exact_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_largejump_signed_to_nonnegative_campbell
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_large_negative_real_integral_signed_abs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original signed Campbell mean from pathwise negativity and exact absolute Campbell mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      (∫ ω, avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω ∂P) =
        (t : ℝ) * (∫ z in Iic (-1 : ℝ), z ∂X.ν) := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro t
  have hPhysical :=
    avram_ja18g_original_largejump_signed_to_nonnegative_campbell
      X hX hFinite t
  have hCampbell :=
    avram_ja18q1_original_largejump_Campbell_exact_nonnegative X t
  have hSigned :=
    avram_ja18g_original_large_negative_real_integral_signed_abs
      X hX hFinite
  calc
    (∫ ω, avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω ∂P) =
      - (∫⁻ ω, ∫⁻ p in (Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)),
          ENNReal.ofReal |p.2| ∂((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P).toReal :=
        hPhysical
    _ = - ((t : ℝ≥0∞) *
          (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν)).toReal := by
        rw [hCampbell]
    _ = - (t : ℝ) *
          (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν).toReal := by
        simp only [ENNReal.toReal_mul, ENNReal.coe_toReal]
        ring
    _ = (t : ℝ) * (∫ z in Iic (-1 : ℝ), z ∂X.ν) := by
        rw [hSigned]
        ring
