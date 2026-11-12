-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_b19_diffuse_finite_mark_rate_continuous_within_cap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T13:52:39.427459+00:00
-- url     : https://prove2.me/submissions/42cac929-862f-4326-b514-1e6ed62835df

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb_phys132_original_finite_cap_uniform_negative_mark_increment_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (hw_meas : Measurable w)
    (ν : Measure ℝ) (hνfinite : ν (Iio (0 : ℝ)) < ⊤)
    (hνatom : ∀ a : ℝ, ν {a} = 0)
    (b₀ : ℝ) (hb₀ : 0 ≤ b₀) (hbC : ENNReal.ofReal b₀ ≤ C) :
    ContinuousWithinAt
      (fun b : ℝ => ∫ z in Iio (0 : ℝ), w (b + z) - w b ∂ν)
      {b : ℝ | 0 ≤ b ∧ ENNReal.ofReal b ≤ C} b₀ := by
  classical
  let s : Set ℝ := {b | 0 ≤ b ∧ ENNReal.ofReal b ≤ C}
  let μ : Measure ℝ := ν.restrict (Iio (0 : ℝ))
  obtain ⟨M, hM, hMbound⟩ :=
    avram_bvb_phys132_original_finite_cap_uniform_negative_mark_increment_bound
      C hFinite w hw_cont hw_neg
  letI : IsFiniteMeasure μ := ⟨by simpa [μ] using hνfinite⟩
  have hboundInt : Integrable (fun _ : ℝ => 2 * M) μ := integrable_const _
  have hmeas (b : ℝ) :
      AEStronglyMeasurable (fun z : ℝ => w (b + z) - w b) μ := by
    have hshift : Measurable (fun z : ℝ => b + z) :=
      measurable_const.add measurable_id
    exact ((hw_meas.comp hshift).sub measurable_const).aestronglyMeasurable
  have hmeasEv : ∀ᶠ b in 𝓝[s] b₀,
      AEStronglyMeasurable (fun z : ℝ => w (b + z) - w b) μ :=
    Filter.Eventually.of_forall hmeas
  have hdom : ∀ᶠ b in 𝓝[s] b₀,
      ∀ᵐ z ∂μ, ‖w (b + z) - w b‖ ≤ 2 * M := by
    filter_upwards [self_mem_nhdsWithin] with b hb
    filter_upwards [MeasureTheory.ae_restrict_mem (μ := ν) measurableSet_Iio] with z hz
    simpa [Real.norm_eq_abs] using hMbound b z hb.1 hb.2 hz
  have hsingle : μ ({-b₀} : Set ℝ) = 0 := by
    have hle : μ ({-b₀} : Set ℝ) ≤ ν { -b₀ } :=
      Measure.restrict_apply_le _ _
    exact le_antisymm (by simpa [hνatom] using hle) (by positivity)
  have hne : ∀ᵐ z ∂μ, z ≠ -b₀ := by
    rw [ae_iff]
    simpa using hsingle
  have hcont : ∀ᵐ z ∂μ,
      ContinuousWithinAt (fun b : ℝ => w (b + z) - w b) s b₀ := by
    filter_upwards [hne] with z hz
    have hbbase : ContinuousWithinAt w s b₀ :=
      (hw_cont b₀ hb₀).mono (fun _ hb => hb.1)
    have hz0 : b₀ + z ≠ 0 := by
      intro hzero
      apply hz
      linarith
    have hwAt : ContinuousAt w (b₀ + z) := by
      rcases lt_or_gt_of_ne hz0 with hneg | hpos
      · have heq : w =ᶠ[𝓝 (b₀ + z)] (fun _ : ℝ => 0) := by
          filter_upwards [isOpen_Iio.mem_nhds hneg] with y hy
          exact hw_neg y hy
        exact continuousAt_const.congr_of_eventuallyEq heq
      · have hmem : Ici (0 : ℝ) ∈ 𝓝 (b₀ + z) :=
          mem_of_superset (isOpen_Ioi.mem_nhds hpos) (by
            intro y hy
            exact le_of_lt (show 0 < y from hy))
        exact hw_cont.continuousAt hmem
    exact (show ContinuousAt (fun b : ℝ => w (b + z)) b₀ from
      hwAt.comp_of_eq (show ContinuousAt (fun b : ℝ => b + z) b₀ from
        continuousAt_id.add continuousAt_const) rfl).continuousWithinAt.sub hbbase
  have hresult :
      ContinuousWithinAt (fun b : ℝ => ∫ z, w (b + z) - w b ∂μ) s b₀ :=
    MeasureTheory.continuousWithinAt_of_dominated
      hmeasEv hdom hboundInt hcont
  simpa only [s, μ] using hresult
