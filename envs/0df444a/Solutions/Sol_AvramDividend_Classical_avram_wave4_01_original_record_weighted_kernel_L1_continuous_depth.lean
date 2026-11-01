-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_weighted_kernel_L1_continuous_depth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:50:29.97463+00:00
-- url     : https://prove2.me/submissions/ae55339c-6fdd-429d-b8a8-a92e9e62d9f5

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

/-- The actual first-record Esscher spatial kernel varies in L1
under a positive reflected drawdown depth perturbation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (θ a : ℝ) (hθ : -φ < θ) (ha : 0 < a) :
    Tendsto (fun b : ℝ =>
      ∫ h : ℝ in Ioi 0,
        |(Real.exp (-(θ * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X b ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal) - (Real.exp (-(θ * h)) *
          (∫⁻ ω, if twoSidedExitUpTime X h ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (Real.exp (-(q *
              (twoSidedExitUpTime X h ω).toReal)))
          else 0 ∂P).toReal)|)
      (𝓝[Ioi (0 : ℝ)] a) (𝓝 (0 : ℝ)) := by
  let K : ℝ → ℝ → ℝ := fun b h =>
    Real.exp (-(θ * h)) *
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
                  barrierRuinTime X b ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal
  change Tendsto (fun b : ℝ =>
    ∫ h : ℝ in Ioi 0, |K b h - K a h|)
      (𝓝[Ioi (0 : ℝ)] a) (𝓝 (0 : ℝ))
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hev : ∀ᶠ b : ℝ in 𝓝[Ioi (0 : ℝ)] a, 0 < b :=
    eventually_mem_nhdsWithin
  have hint (b : ℝ) (hb : 0 < b) :
      Integrable (K b) μ :=
    avram_wave4_01_original_record_weighted_esscher_height_integrable
      X q hq W hW hvar φ hφ hroot b θ hb hθ
  have hintDiff (b : ℝ) (hb : 0 < b) :
      Integrable (fun h : ℝ => |K b h - K a h|) μ :=
    ((hint b hb).sub (hint a ha)).abs
  have hmeas : ∀ᶠ b : ℝ in 𝓝[Ioi (0 : ℝ)] a,
      AEStronglyMeasurable (fun h : ℝ => |K b h - K a h|) μ := by
    filter_upwards [hev] with b hb
    exact (hintDiff b hb).aestronglyMeasurable
  have hM0 : IntegrableOn (fun h : ℝ =>
      Real.exp ((-(θ + φ)) * h)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (a := -(θ + φ)) (by linarith) 0
  have hM : Integrable (fun h : ℝ =>
      Real.exp (-((θ + φ) * h))) μ := by
    change IntegrableOn (fun h : ℝ =>
      Real.exp (-((θ + φ) * h))) (Ioi 0)
    simpa only [neg_mul] using hM0
  have hdom : ∀ᶠ b : ℝ in 𝓝[Ioi (0 : ℝ)] a,
      ∀ᵐ h ∂μ, ‖|K b h - K a h|‖ ≤
        Real.exp (-((θ + φ) * h)) := by
    filter_upwards [hev] with b hb
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := (volume : Measure ℝ)) measurableSet_Ioi] with h hh
    rw [Real.norm_eq_abs, abs_abs]
    have hbnd :=
      avram_wave4_01_original_record_weighted_esscher_pointwise_domination
        X q hq W hW hvar φ hφ hroot θ b h hb hh
    have hand :=
      avram_wave4_01_original_record_weighted_esscher_pointwise_domination
        X q hq W hW hvar φ hφ hroot θ a h ha hh
    exact abs_sub_le_iff.mpr
      ⟨by linarith [hbnd.1, hand.2], by linarith [hand.1, hbnd.2]⟩
  have hsource :=
    avram_wave4_01_original_record_survival_joint_continuous_height_depth
      X q hq W hW hvar
  have hpoint (h : ℝ) (hh : 0 < h) :
      Tendsto (fun b : ℝ => |K b h - K a h|)
        (𝓝[Ioi (0 : ℝ)] a) (𝓝 (0 : ℝ)) := by
    have hpair : ContinuousOn (fun b : ℝ => (h, b))
        (Ioi (0 : ℝ)) :=
      (continuous_const.prodMk continuous_id).continuousOn
    have hG : ContinuousOn (fun b : ℝ =>
        (∫⁻ ω, if twoSidedExitUpTime X h ω <
                    barrierRuinTime X b ω then
          ENNReal.ofReal (Real.exp (-(q *
            (twoSidedExitUpTime X h ω).toReal)))
        else 0 ∂P).toReal) (Ioi 0) := by
      simpa only [Function.comp_def] using
        (hsource.comp hpair (by
          intro b hb
          exact ⟨hh, hb⟩))
    have hC : ContinuousOn (fun _ : ℝ =>
        Real.exp (-(θ * h))) (Ioi 0) := continuousOn_const
    have hK : ContinuousOn (fun b : ℝ => K b h) (Ioi 0) := by
      apply (hC.mul hG).congr
      intro b hb
      dsimp [K]
    have hc : Tendsto (fun b : ℝ => K b h)
        (𝓝[Ioi (0 : ℝ)] a) (𝓝 (K a h)) :=
      (hK.continuousWithinAt ha).tendsto
    have hconst : Tendsto (fun _ : ℝ => K a h)
        (𝓝[Ioi (0 : ℝ)] a) (𝓝 (K a h)) :=
      tendsto_const_nhds
    have hdiff : Tendsto (fun b : ℝ => K b h - K a h)
        (𝓝[Ioi (0 : ℝ)] a) (𝓝 (K a h - K a h)) :=
      hc.sub hconst
    have habs : Tendsto (fun b : ℝ => |K b h - K a h|)
        (𝓝[Ioi (0 : ℝ)] a) (𝓝 (|K a h - K a h|)) :=
      hdiff.abs
    simpa only [sub_self, abs_zero] using habs
  have hlim : ∀ᵐ h ∂μ,
      Tendsto (fun b : ℝ => |K b h - K a h|)
        (𝓝[Ioi (0 : ℝ)] a) (𝓝 (0 : ℝ)) := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict
      (μ := (volume : Measure ℝ)) measurableSet_Ioi] with h hh
    exact hpoint h hh
  have hDCT :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (F := fun b h => |K b h - K a h|)
      (f := fun _ => (0 : ℝ))
      (fun h : ℝ => Real.exp (-((θ + φ) * h)))
      hmeas hdom hM hlim
  simpa only [integral_zero, μ] using hDCT
