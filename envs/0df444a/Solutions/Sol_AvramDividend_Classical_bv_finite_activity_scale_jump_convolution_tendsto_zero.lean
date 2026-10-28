-- Prove2me | solution 1 for AvramDividend.Classical.bv_finite_activity_scale_jump_convolution_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:29:45.532821+00:00
-- url     : https://prove2.me/submissions/868414ba-e8e4-4a0a-ba28-32860d0072da

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

/-- Finite jump mass and scale monotonicity imply vanishing of the jump convolution at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) :
    Tendsto (fun x : ℝ =>
      ∫ y in Iio (0 : ℝ), W (x + y) ∂X.ν)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
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
  have hFmeas : ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0),
      AEStronglyMeasurable (fun y : ℝ => W (x + y)) μ :=
    Eventually.of_forall (fun x =>
      (hmeas.comp (measurable_const.add measurable_id)).aestronglyMeasurable)
  have hsmall : ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0),
      0 < x ∧ x < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.mem_inf_of_left (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with x hx hlt
    exact ⟨mem_Ioi.mp hx, mem_Iio.mp hlt⟩
  have hbound : ∀ᶠ x : ℝ in nhdsWithin 0 (Ioi 0),
      ∀ᵐ y : ℝ ∂μ, ‖W (x + y)‖ ≤ W 1 := by
    filter_upwards [hsmall] with x hx
    filter_upwards [hneg] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg (x + y))]
    by_cases hxy : x + y < 0
    · rw [hW.1 (x + y) hxy]
      exact hnonneg 1
    · have hlo : 0 ≤ x + y := le_of_not_gt hxy
      have hhi : x + y ≤ 1 := by linarith [hx.2, hy]
      exact hW.2.2.2.1 (mem_Ici.mpr hlo)
        (mem_Ici.mpr (by norm_num)) hhi
  have hlim : ∀ᵐ y : ℝ ∂μ,
      Tendsto (fun x : ℝ => W (x + y))
        (nhdsWithin 0 (Ioi 0)) (nhds (0 : ℝ)) := by
    filter_upwards [hneg] with y hy
    have hevent : (fun x : ℝ => W (x + y)) =ᶠ[
        nhdsWithin 0 (Ioi 0)] (fun _ => 0) := by
      filter_upwards [Filter.mem_inf_of_left
        (Iio_mem_nhds (by linarith : (0 : ℝ) < -y))]
        with x hx
      exact hW.1 (x + y) (by linarith [mem_Iio.mp hx])
    exact tendsto_const_nhds.congr' hevent.symm
  have ht := tendsto_integral_filter_of_norm_le_const
    (μ := μ) (l := nhdsWithin (0 : ℝ) (Ioi 0))
    (F := fun x y => W (x + y)) (f := fun _ => (0 : ℝ))
    hFmeas ⟨W 1, hbound⟩ hlim
  simpa [μ] using ht
