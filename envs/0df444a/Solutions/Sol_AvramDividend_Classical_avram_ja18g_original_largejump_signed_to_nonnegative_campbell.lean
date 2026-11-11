-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18g_original_largejump_signed_to_nonnegative_campbell
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T03:27:14.001215+00:00
-- url     : https://prove2.me/submissions/69c2cb43-263e-44e0-bcb2-41057dc5d04e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18q1_original_largejump_Campbell_exact_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_large_negative_signed_mark_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_largejump_sum_L1_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_ja18g_original_large_mark_absolute_mass_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- On the original sample space, negative jump marks convert signed cash into the
exact finite nonnegative Campbell mass, with no auxiliary marked process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ t : ℝ≥0,
      (∫ ω, avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω ∂P) =
      - (∫⁻ ω, ∫⁻ p in (Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)),
        ENNReal.ofReal |p.2| ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) ∂P).toReal := by
  letI : IsProbabilityMeasure P := X.isProbability
  intro t
  let B : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) t ×ˢ Iic (-1 : ℝ)
  let N (ω : Ω) : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  let A (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ p in B, ENNReal.ofReal |p.2| ∂N ω
  have hB : MeasurableSet B := measurableSet_Ioc.prod measurableSet_Iic
  have hPhysical (ω : Ω) :
      avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω = -(A ω).toReal := by
    unfold avram_p4_h_gaussian_intrinsic_large_jump_sum
    change (∫ p in B, p.2 ∂N ω) = -(A ω).toReal
    have hSign : (∫ p in B, p.2 ∂N ω) =
        - (∫ p in B, |p.2| ∂N ω) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hB] with p hp
      have hp0 : p.2 ≤ 0 := le_trans hp.2 (by norm_num)
      simp [abs_of_nonpos hp0]
    rw [hSign]
    congr 1
    apply integral_eq_lintegral_of_nonneg_ae
    · exact Filter.Eventually.of_forall (fun p => abs_nonneg p.2)
    · exact (measurable_snd.abs).aestronglyMeasurable
  have hNu : (∫⁻ z in Iic (-1 : ℝ), ENNReal.ofReal |z| ∂X.ν) < ⊤ := by
    have hInt : Integrable (fun z : ℝ => z) (X.ν.restrict (Iic (-1 : ℝ))) :=
      avram_ja18g_original_large_negative_signed_mark_integrable X hX
    have hFin := hInt.hasFiniteIntegral
    change (∫⁻ z, ‖z‖ₑ ∂(X.ν.restrict (Iic (-1 : ℝ)))) < ⊤ at hFin
    simpa only [Real.enorm_eq_ofReal_abs] using hFin
  have hCampbell :
      (∫⁻ ω, A ω ∂P) =
        (t : ℝ≥0∞) * (∫⁻ z in Iic (-1 : ℝ),
          ENNReal.ofReal |z| ∂X.ν) := by
    simpa only [A, B, N] using
      (avram_ja18q1_original_largejump_Campbell_exact_nonnegative X t)
  have hAMeanFinite : (∫⁻ ω, A ω ∂P) < ⊤ := by
    rw [hCampbell]
    exact ENNReal.mul_lt_top (by simp) hNu
  have hMeasA : Measurable A := by
    simpa only [A, B, N] using
      (avram_ja18g_original_large_mark_absolute_mass_measurable X hX t)
  have hAFinite : ∀ᵐ ω ∂P, A ω ≠ ⊤ := by
    filter_upwards [ae_lt_top hMeasA (ne_of_lt hAMeanFinite)] with ω hω
    exact ne_of_lt hω
  have hJ : Integrable (avram_p4_h_gaussian_intrinsic_large_jump_sum X t) P :=
    avram_ja18_original_largejump_sum_L1_of_standing X hX hFinite t
  have hARealMeas : AEStronglyMeasurable (fun ω => (A ω).toReal) P := by
    have hFun : (fun ω => (A ω).toReal) =
        (fun ω => -avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω) := by
      funext ω
      linarith [hPhysical ω]
    rw [hFun]
    exact hJ.neg.aestronglyMeasurable
  have hMean :
      (∫ ω, (A ω).toReal ∂P) = (∫⁻ ω, A ω ∂P).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun ω => ENNReal.toReal_nonneg)) hARealMeas]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hAFinite] with ω hω
    exact ENNReal.ofReal_toReal hω
  calc
    (∫ ω, avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω ∂P) =
        ∫ ω, -(A ω).toReal ∂P := integral_congr_ae
          (Filter.Eventually.of_forall (fun ω => hPhysical ω))
    _ = - (∫ ω, (A ω).toReal ∂P) := by rw [integral_neg]
    _ = - (∫⁻ ω, A ω ∂P).toReal := by rw [hMean]
