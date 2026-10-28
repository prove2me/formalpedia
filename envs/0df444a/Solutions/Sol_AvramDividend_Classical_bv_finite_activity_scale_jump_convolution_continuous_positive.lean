-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_scale_jump_convolution_continuous_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:59:04.98729+00:00
-- url     : https://prove2.me/submissions/ed5d2799-0506-40c9-87c5-14e7121aa5e6

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_continuousAt_away_zero
import Theorems.Thm_AvramDividend_Classical_levyMeasure_singleton_null_of_standing_boundedVariation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

/-- The diffuse finite negative-jump measure smooths the scale function's origin discontinuity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    ContinuousOn (fun x : ℝ =>
      ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)
      (Ioi (0 : ℝ)) := by
  let μ : Measure ℝ := X.ν.restrict (Iio (0 : ℝ))
  haveI : IsFiniteMeasure μ := ⟨by simpa [μ] using hFinite⟩
  have hmeas : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hnonneg (z : ℝ) : 0 ≤ W z := by
    by_cases hz : z < 0
    · rw [hW.1 z hz]
    · exact hW.2.1 z (le_of_not_gt hz)
  have hneg : ∀ᵐ y : ℝ ∂μ, y < 0 := by
    simpa only [mem_Iio] using (ae_restrict_mem (μ := X.ν) measurableSet_Iio)
  intro a ha
  have hνnull : X.ν ({-a} : Set ℝ) = 0 :=
    levyMeasure_singleton_null_of_standing_boundedVariation X hX hBV (-a)
  have hμnull : μ ({-a} : Set ℝ) = 0 := by
    apply le_antisymm
    · exact (Measure.restrict_apply_le (Iio (0 : ℝ)) ({-a} : Set ℝ)).trans_eq hνnull
    · exact bot_le
  have hAE : ∀ᵐ y : ℝ ∂μ, y ≠ -a := by
    apply ae_iff.mpr
    have hset : {y : ℝ | ¬ y ≠ -a} = ({-a} : Set ℝ) := by ext y; simp
    simpa only [hset] using hμnull
  have hFmeas : ∀ᶠ x : ℝ in nhds a,
      AEStronglyMeasurable (fun y : ℝ => W (x + y)) μ :=
    Eventually.of_forall (fun x =>
      (hmeas.comp (measurable_const.add measurable_id)).aestronglyMeasurable)
  have hsmall : ∀ᶠ x : ℝ in nhds a, x < a + 1 :=
    Iio_mem_nhds (by linarith)
  have hbound : ∀ᶠ x : ℝ in nhds a,
      ∀ᵐ y : ℝ ∂μ, ‖W (x + y)‖ ≤ W (a + 1) := by
    filter_upwards [hsmall] with x hx
    filter_upwards [hneg] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg (x + y))]
    by_cases hxy : x + y < 0
    · rw [hW.1 (x + y) hxy]
      exact hnonneg (a + 1)
    · have hlo : 0 ≤ x + y := le_of_not_gt hxy
      have hhi : x + y ≤ a + 1 := by linarith
      exact hW.2.2.2.1 (mem_Ici.mpr hlo)
        (mem_Ici.mpr (by linarith [mem_Ioi.mp ha])) hhi
  have hlim : ∀ᵐ y : ℝ ∂μ,
      Tendsto (fun x : ℝ => W (x + y)) (nhds a)
        (nhds (W (a + y))) := by
    filter_upwards [hAE] with y hy
    have hne : a + y ≠ 0 := by
      intro heq
      apply hy
      linarith [heq]
    have hplus : ContinuousAt (fun x : ℝ => x + y) a := continuousAt_id.add continuousAt_const
    have hW_at : ContinuousAt W (a + y) := scaleFunction_continuousAt_away_zero X q W hW (a + y) hne
    have hW_comp : ContinuousAt (fun x : ℝ => W (x + y)) a :=
      ContinuousAt.comp (f := fun x : ℝ => x + y) (g := W) (x := a) hW_at hplus
    exact hW_comp.tendsto
  have ht := tendsto_integral_filter_of_norm_le_const
    (μ := μ) (l := nhds a) (F := fun x y => W (x + y)) (f := fun y => W (a + y))
    hFmeas ⟨W (a + 1), hbound⟩ hlim
  have hcont : ContinuousAt (fun x : ℝ => ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν) a := by
    change Tendsto (fun x : ℝ => ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)
      (nhds a) (nhds (∫ y in Iio (0 : ℝ), W (a + y) ∂X.ν))
    simpa only [μ] using ht
  exact hcont.continuousWithinAt
