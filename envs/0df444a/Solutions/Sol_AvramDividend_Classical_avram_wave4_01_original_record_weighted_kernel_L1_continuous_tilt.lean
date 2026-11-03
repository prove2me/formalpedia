-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_weighted_kernel_L1_continuous_tilt
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:29:16.651075+00:00
-- url     : https://prove2.me/submissions/1d160f6a-c835-4abf-920f-3dc6a71d17ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_esscher_pointwise_domination
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_weighted_esscher_height_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a θ₀ : ℝ) (ha : 0 < a) (hθ₀ : -φ < θ₀) :
    Tendsto (fun θ : ℝ =>
      ∫ h : ℝ in Ioi 0,
        |(Real.exp (-(θ * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal) - (Real.exp (-(θ₀ * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal)|)
      (𝓝[Ioi (-φ)] θ₀) (𝓝 (0 : ℝ)) := by
  let K : ℝ → ℝ → ℝ := fun θ h =>
    Real.exp (-(θ * h)) *
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
                  barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal
  change Tendsto (fun θ : ℝ =>
    ∫ h : ℝ in Ioi 0, |K θ h - K θ₀ h|)
      (𝓝[Ioi (-φ)] θ₀) (𝓝 (0 : ℝ))
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let θlo : ℝ := (θ₀ - φ) / 2
  have hlo0 : θlo < θ₀ := by dsimp [θlo]; linarith
  have hposlo : 0 < θlo + φ := by dsimp [θlo]; linarith
  have hevlo : ∀ᶠ θ : ℝ in 𝓝[Ioi (-φ)] θ₀, θlo < θ := by
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (isOpen_Ioi.mem_nhds hlo0)
  have hev : ∀ᶠ θ : ℝ in 𝓝[Ioi (-φ)] θ₀,
      θlo < θ ∧ -φ < θ := by
    filter_upwards [hevlo, eventually_mem_nhdsWithin] with θ hlt hmem
    exact ⟨hlt, hmem⟩
  have hint (θ : ℝ) (hθ : -φ < θ) :
      Integrable (K θ) μ :=
    avram_wave4_01_original_record_weighted_esscher_height_integrable
      X q hq W hW hvar φ hφ hroot a θ ha hθ
  have hmeas : ∀ᶠ θ : ℝ in 𝓝[Ioi (-φ)] θ₀,
      AEStronglyMeasurable (fun h : ℝ => |K θ h - K θ₀ h|) μ := by
    filter_upwards [hev] with θ hh
    exact (((hint θ hh.2).sub (hint θ₀ hθ₀)).abs).aestronglyMeasurable
  have hM0 : IntegrableOn (fun h : ℝ =>
      Real.exp ((-(θlo + φ)) * h)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (a := -(θlo + φ)) (by linarith) 0
  have hM : Integrable (fun h : ℝ =>
      Real.exp (-((θlo + φ) * h))) μ := by
    change IntegrableOn (fun h : ℝ =>
      Real.exp (-((θlo + φ) * h))) (Ioi 0)
    simpa only [neg_mul] using hM0
  have hdom : ∀ᶠ θ : ℝ in 𝓝[Ioi (-φ)] θ₀,
      ∀ᵐ h ∂μ, ‖|K θ h - K θ₀ h|‖ ≤
        Real.exp (-((θlo + φ) * h)) := by
    filter_upwards [hev] with θ hhθ
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := (volume : Measure ℝ)) measurableSet_Ioi] with h hh
    rw [Real.norm_eq_abs, abs_abs]
    have hbnd :=
      avram_wave4_01_original_record_weighted_esscher_pointwise_domination
        X q hq W hW hvar φ hφ hroot θ a h ha hh
    have hand :=
      avram_wave4_01_original_record_weighted_esscher_pointwise_domination
        X q hq W hW hvar φ hφ hroot θ₀ a h ha hh
    have hbM : Real.exp (-((θ + φ) * h)) ≤
        Real.exp (-((θlo + φ) * h)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg
        (mul_le_mul_of_nonneg_right (by linarith : θlo + φ ≤ θ + φ)
          (le_of_lt hh))
    have haM : Real.exp (-((θ₀ + φ) * h)) ≤
        Real.exp (-((θlo + φ) * h)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg
        (mul_le_mul_of_nonneg_right (by linarith : θlo + φ ≤ θ₀ + φ)
          (le_of_lt hh))
    exact abs_sub_le_iff.mpr
      ⟨by linarith [hbnd.1, hand.2, haM],
       by linarith [hand.1, hbnd.2, hbM]⟩
  have hpoint (h : ℝ) (_hh : 0 < h) :
      Tendsto (fun θ : ℝ => |K θ h - K θ₀ h|)
        (𝓝[Ioi (-φ)] θ₀) (𝓝 (0 : ℝ)) := by
    have harg : Continuous (fun θ : ℝ => -(θ * h)) :=
      (continuous_id.mul continuous_const).neg
    have he : Continuous (fun θ : ℝ => Real.exp (-(θ * h))) :=
      Real.continuous_exp.comp harg
    have hK : Continuous (fun θ : ℝ => K θ h) := by
      dsimp [K]
      exact he.mul continuous_const
    have hc : Tendsto (fun θ : ℝ => K θ h)
        (𝓝[Ioi (-φ)] θ₀) (𝓝 (K θ₀ h)) :=
      (hK.continuousOn.continuousWithinAt hθ₀).tendsto
    have hconst : Tendsto (fun _ : ℝ => K θ₀ h)
        (𝓝[Ioi (-φ)] θ₀) (𝓝 (K θ₀ h)) :=
      tendsto_const_nhds
    have hdiff : Tendsto (fun θ : ℝ => K θ h - K θ₀ h)
        (𝓝[Ioi (-φ)] θ₀) (𝓝 (K θ₀ h - K θ₀ h)) :=
      hc.sub hconst
    have habs : Tendsto (fun θ : ℝ => |K θ h - K θ₀ h|)
        (𝓝[Ioi (-φ)] θ₀) (𝓝 (|K θ₀ h - K θ₀ h|)) :=
      hdiff.abs
    simpa only [sub_self, abs_zero] using habs
  have hlim : ∀ᵐ h ∂μ,
      Tendsto (fun θ : ℝ => |K θ h - K θ₀ h|)
        (𝓝[Ioi (-φ)] θ₀) (𝓝 (0 : ℝ)) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := (volume : Measure ℝ)) measurableSet_Ioi] with h hh
    exact hpoint h hh
  have hDCT :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (F := fun θ h => |K θ h - K θ₀ h|)
      (f := fun _ => (0 : ℝ))
      (fun h : ℝ => Real.exp (-((θlo + φ) * h)))
      hmeas hdom hM hlim
  simpa only [integral_zero, μ] using hDCT
