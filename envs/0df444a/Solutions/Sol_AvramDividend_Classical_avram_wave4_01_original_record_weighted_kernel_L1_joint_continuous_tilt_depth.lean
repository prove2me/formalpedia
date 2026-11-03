-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_weighted_kernel_L1_joint_continuous_tilt_depth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T07:56:50.58419+00:00
-- url     : https://prove2.me/submissions/e9b9eb81-8709-45f3-9cf7-7a6c2105182b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_survival_joint_continuous_height_depth
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
    (θ₀ a : ℝ) (hθ₀ : -φ < θ₀) (ha : 0 < a) :
    Tendsto (fun p : ℝ × ℝ =>
      ∫ h : ℝ in Ioi 0,
        |(Real.exp (-(p.1 * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X p.2 ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal) - (Real.exp (-(θ₀ * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal)|)
      (𝓝[(Ioi (-φ)).prod (Ioi (0 : ℝ))] (θ₀, a)) (𝓝 (0 : ℝ)) := by
  let F : (ℝ × ℝ) → ℝ := fun z =>
    (∫⁻ ω, if twoSidedExitUpTime X z.1 ω <
      barrierRuinTime X z.2 ω then
      ENNReal.ofReal (Real.exp (-(q *
        (twoSidedExitUpTime X z.1 ω).toReal)))
    else 0 ∂P).toReal
  let K : (ℝ × ℝ) → ℝ → ℝ := fun p h =>
    Real.exp (-(p.1 * h)) * F (h, p.2)
  change Tendsto (fun p : ℝ × ℝ =>
    ∫ h : ℝ in Ioi 0, |K p h - K (θ₀, a) h|)
      (𝓝[(Ioi (-φ)).prod (Ioi (0 : ℝ))] (θ₀, a)) (𝓝 (0 : ℝ))
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let s : Set (ℝ × ℝ) := (Ioi (-φ)).prod (Ioi (0 : ℝ))
  let p₀ : ℝ × ℝ := (θ₀, a)
  let θlo : ℝ := (θ₀ - φ) / 2
  have hlo0 : θlo < θ₀ := by dsimp [θlo]; linarith
  have hposlo : 0 < θlo + φ := by dsimp [θlo]; linarith
  have hevlo : ∀ᶠ p : ℝ × ℝ in 𝓝[s] p₀, θlo < p.1 := by
    have hnear : ∀ᶠ p : ℝ × ℝ in 𝓝 p₀, θlo < p.1 :=
      (continuous_fst.tendsto p₀).eventually (isOpen_Ioi.mem_nhds hlo0)
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hnear
  have hev : ∀ᶠ p : ℝ × ℝ in 𝓝[s] p₀,
      θlo < p.1 ∧ -φ < p.1 ∧ 0 < p.2 := by
    filter_upwards [hevlo, eventually_mem_nhdsWithin] with p hlo hp
    exact ⟨hlo, hp.1, hp.2⟩
  have hint (p : ℝ × ℝ) (hp : -φ < p.1 ∧ 0 < p.2) :
      Integrable (K p) μ :=
    avram_wave4_01_original_record_weighted_esscher_height_integrable
      X q hq W hW hvar φ hφ hroot p.2 p.1 hp.2 hp.1
  have hmeas : ∀ᶠ p : ℝ × ℝ in 𝓝[s] p₀,
      AEStronglyMeasurable (fun h : ℝ => |K p h - K p₀ h|) μ := by
    filter_upwards [hev] with p hp
    exact (((hint p ⟨hp.2.1, hp.2.2⟩).sub
      (hint p₀ ⟨hθ₀, ha⟩)).abs).aestronglyMeasurable
  have hM0 : IntegrableOn (fun h : ℝ =>
      Real.exp ((-(θlo + φ)) * h)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (a := -(θlo + φ)) (by linarith) 0
  have hM : Integrable (fun h : ℝ =>
      Real.exp (-((θlo + φ) * h))) μ := by
    change IntegrableOn (fun h : ℝ =>
      Real.exp (-((θlo + φ) * h))) (Ioi 0)
    simpa only [neg_mul] using hM0
  have hdom : ∀ᶠ p : ℝ × ℝ in 𝓝[s] p₀,
      ∀ᵐ h ∂μ, ‖|K p h - K p₀ h|‖ ≤
        Real.exp (-((θlo + φ) * h)) := by
    filter_upwards [hev] with p hp
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := (volume : Measure ℝ)) measurableSet_Ioi] with h hh
    rw [Real.norm_eq_abs, abs_abs]
    have hbnd :=
      avram_wave4_01_original_record_weighted_esscher_pointwise_domination
        X q hq W hW hvar φ hφ hroot p.1 p.2 h hp.2.2 hh
    have hand :=
      avram_wave4_01_original_record_weighted_esscher_pointwise_domination
        X q hq W hW hvar φ hφ hroot θ₀ a h ha hh
    have hbM : Real.exp (-((p.1 + φ) * h)) ≤
        Real.exp (-((θlo + φ) * h)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg
        (mul_le_mul_of_nonneg_right
          (by linarith : θlo + φ ≤ p.1 + φ) (le_of_lt hh))
    have haM : Real.exp (-((θ₀ + φ) * h)) ≤
        Real.exp (-((θlo + φ) * h)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg
        (mul_le_mul_of_nonneg_right
          (by linarith : θlo + φ ≤ θ₀ + φ) (le_of_lt hh))
    exact abs_sub_le_iff.mpr
      ⟨by linarith [hbnd.1, hand.2, haM],
       by linarith [hand.1, hbnd.2, hbM]⟩
  have hsurv : ContinuousOn F (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) :=
    avram_wave4_01_original_record_survival_joint_continuous_height_depth
      X q hq W hW hvar
  have hpoint (h : ℝ) (hh : 0 < h) :
      Tendsto (fun p : ℝ × ℝ => |K p h - K p₀ h|)
        (𝓝[s] p₀) (𝓝 (0 : ℝ)) := by
    have hF : ContinuousAt F (h, a) :=
      hsurv.continuousAt
        ((isOpen_Ioi.prod isOpen_Ioi).mem_nhds ⟨hh, ha⟩)
    have hFparam : ContinuousAt (fun p : ℝ × ℝ => F (h, p.2)) p₀ :=
      ContinuousAt.comp (f := fun p : ℝ × ℝ => (h, p.2))
        (g := F) (x := p₀) hF
        ((continuous_const.prodMk continuous_snd).continuousAt)
    have he : ContinuousAt (fun p : ℝ × ℝ =>
        Real.exp (-(p.1 * h))) p₀ :=
      (Real.continuous_exp.comp
        ((continuous_fst.mul continuous_const).neg)).continuousAt
    have hK : ContinuousAt (fun p : ℝ × ℝ => K p h) p₀ := by
      exact he.mul hFparam
    have hc : Tendsto (fun p : ℝ × ℝ => K p h)
        (𝓝[s] p₀) (𝓝 (K p₀ h)) :=
      hK.continuousWithinAt.tendsto
    have hdiff : Tendsto (fun p : ℝ × ℝ => K p h - K p₀ h)
        (𝓝[s] p₀) (𝓝 (K p₀ h - K p₀ h)) :=
      hc.sub tendsto_const_nhds
    simpa only [sub_self, abs_zero] using hdiff.abs
  have hlim : ∀ᵐ h ∂μ,
      Tendsto (fun p : ℝ × ℝ => |K p h - K p₀ h|)
        (𝓝[s] p₀) (𝓝 (0 : ℝ)) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := (volume : Measure ℝ)) measurableSet_Ioi] with h hh
    exact hpoint h hh
  have hDCT :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (F := fun p h => |K p h - K p₀ h|)
      (f := fun _ => (0 : ℝ))
      (fun h : ℝ => Real.exp (-((θlo + φ) * h)))
      hmeas hdom hM hlim
  simpa only [integral_zero, μ, s, p₀] using hDCT
