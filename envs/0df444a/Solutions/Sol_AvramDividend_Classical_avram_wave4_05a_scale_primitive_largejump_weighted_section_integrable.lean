-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05a_scale_primitive_largejump_weighted_section_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:02:53.243408+00:00
-- url     : https://prove2.me/submissions/e8edb198-dd6f-4573-9310-e989db1f0249

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_zero_nonpositive
import Theorems.Thm_AvramDividend_Classical_positive_laplace_interval_primitive_real
import Theorems.Thm_AvramDividend_Classical_scaleFunction_intervalIntegrable_nonnegative
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_large_negative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 < θ) (hqθ : q < X.ψ θ) (r : ℝ) (hr : 1 ≤ r) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ*x)) * |SpectrallyNegativeLevy.generatorIntegrand
      (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|) (Ioi (0 : ℝ)) volume ∧
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * |SpectrallyNegativeLevy.generatorIntegrand
      (fun z : ℝ => ∫ t in (0 : ℝ)..z, W t) x (-r)|) ≤ (X.ψ θ - q)⁻¹ / θ := by
  let U : ℝ → ℝ := fun z => ∫ t in (0 : ℝ)..z, W t
  have hUzero (z : ℝ) (hz : z ≤ 0) : U z = 0 := avram_wave4_p2_scale_primitive_zero_nonpositive X q W hW z hz
  have hUnonneg (z : ℝ) (hz : 0 ≤ z) : 0 ≤ U z := by
    change 0 ≤ ∫ t in (0 : ℝ)..z, W t
    exact intervalIntegral.integral_nonneg hz (fun t ht => hW.2.1 t ht.1)
  have hUmono : Monotone U := by
    intro a b hab
    by_cases hb : b ≤ 0
    · rw [hUzero a (hab.trans hb), hUzero b hb]
    · have hb0 : 0 ≤ b := le_of_lt (lt_of_not_ge hb)
      by_cases ha : a ≤ 0
      · rw [hUzero a ha]; exact hUnonneg b hb0
      · have ha0 : 0 ≤ a := le_of_lt (lt_of_not_ge ha)
        have hi : IntervalIntegrable W volume (0 : ℝ) b := scaleFunction_intervalIntegrable_nonnegative X q W hW 0 b (le_refl 0) hb0
        have hWnn : ∀ z : ℝ, 0 ≤ W z := by
          intro z; by_cases hz : 0 ≤ z
          · exact hW.2.1 z hz
          · rw [hW.1 z (lt_of_not_ge hz)]
        have hae : ∀ᵐ z ∂(volume.restrict (Ioc (0 : ℝ) b)), 0 ≤ W z := Filter.Eventually.of_forall hWnn
        exact intervalIntegral.integral_mono_interval (le_refl (0 : ℝ)) ha0 hab hae hi
  have hUnonneg_all (z : ℝ) : 0 ≤ U z := by
    by_cases hz : z ≤ 0
    · rw [hUzero z hz]
    · exact hUnonneg z (le_of_lt (lt_of_not_ge hz))
  have hUmeas : Measurable U := hUmono.measurable
  have hLapW := hW.2.2.2.2 θ hθ.le hqθ
  have hLapU := positive_laplace_interval_primitive_real W θ hθ hLapW.1
  have hUInt : IntegrableOn (fun x : ℝ => Real.exp (-(θ*x)) * U x) (Ioi (0 : ℝ)) volume := hLapU.1
  have hy : -r ≤ (-1 : ℝ) := by linarith
  have hJ (x : ℝ) : SpectrallyNegativeLevy.generatorIntegrand U x (-r) = U (x-r) - U x := by
    convert generatorIntegrand_large_negative U x (-r) hy using 1 <;> ring
  have hle (x : ℝ) : 0 ≤ U x - U (x-r) ∧ U x - U (x-r) ≤ U x := by
    have hmono := hUmono (show x-r ≤ x by linarith)
    have hnn := hUnonneg_all (x-r)
    constructor <;> linarith
  have hmeasShift : Measurable (fun x : ℝ => U (x-r)) :=
    hUmeas.comp (measurable_id.sub measurable_const)
  have hmeasExp : Measurable (fun x : ℝ => Real.exp (-(θ*x))) := by fun_prop
  have hmeasDiff : Measurable (fun x : ℝ => U (x-r) - U x) := hmeasShift.sub hUmeas
  have hmeasAbs : Measurable (fun x : ℝ => |U (x-r) - U x|) := hmeasDiff.abs
  have hmeasJ : Measurable (fun x : ℝ => Real.exp (-(θ*x)) * |SpectrallyNegativeLevy.generatorIntegrand U x (-r)|) := by
    have hh : Measurable (fun x : ℝ => Real.exp (-(θ*x)) * |U (x-r) - U x|) := hmeasExp.mul hmeasAbs
    convert hh using 1
    funext x; rw [hJ x]
  have hpoint (x : ℝ) : Real.exp (-(θ*x)) * |SpectrallyNegativeLevy.generatorIntegrand U x (-r)| ≤ Real.exp (-(θ*x)) * U x := by
    rw [hJ x, abs_sub_comm, abs_of_nonneg (hle x).1]
    exact mul_le_mul_of_nonneg_left (hle x).2 (Real.exp_nonneg _)
  have hJInt : IntegrableOn (fun x : ℝ => Real.exp (-(θ*x)) * |SpectrallyNegativeLevy.generatorIntegrand U x (-r)|) (Ioi (0 : ℝ)) volume := by
    apply hUInt.mono' hmeasJ.aestronglyMeasurable
    filter_upwards [] with x; simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))] using hpoint x
  refine ⟨hJInt, ?_⟩
  calc
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * |SpectrallyNegativeLevy.generatorIntegrand U x (-r)|) ≤ ∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * U x := by
            apply integral_mono_ae hJInt hUInt
            filter_upwards [] with x; exact hpoint x
      _ = (X.ψ θ - q)⁻¹ / θ := by
        change (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) * (∫ t in (0 : ℝ)..x, W t)) = _
        rw [hLapU.2, hLapW.2]
