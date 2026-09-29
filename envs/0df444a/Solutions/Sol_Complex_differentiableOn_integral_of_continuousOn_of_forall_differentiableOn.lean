-- Prove2me | solution 1 for Complex.differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/7588a9dd-2394-5784-8de8-400b8199530a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn

set_option autoImplicit false

open MeasureTheory Filter Metric Set Topology

namespace Q1ParamHol

variable {Y : Type*} [TopologicalSpace Y]

theorem continuous_slice {U : Set ℂ} (F : ℂ → Y → ℂ)
    (hF : ContinuousOn (Function.uncurry F) (U ×ˢ Set.univ)) {z : ℂ} (hz : z ∈ U) :
    Continuous (F z) := by
  have : Continuous fun a : Y => (z, a) := continuous_const.prodMk continuous_id
  exact hF.comp_continuous this (fun a => ⟨hz, trivial⟩)

theorem isOpen_nonzero {U : Set ℂ} (F : ℂ → Y → ℂ)
    (hF : ContinuousOn (Function.uncurry F) (U ×ˢ Set.univ)) :
    IsOpen (⋃ z ∈ U, {a : Y | F z a ≠ 0}) := by
  refine isOpen_biUnion fun z hz => ?_
  exact isOpen_ne_fun (continuous_slice F hF hz) continuous_const

end Q1ParamHol

open Q1ParamHol in
theorem solution
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    (ν : MeasureTheory.Measure Y) [MeasureTheory.IsFiniteMeasureOnCompacts ν]
    {U : Set ℂ} (hU : IsOpen U) {S : Set Y} (hS : IsCompact S)
    (F : ℂ → Y → ℂ) (hF : ContinuousOn (Function.uncurry F) (U ×ˢ Set.univ))
    (hFS : ∀ z ∈ U, ∀ a ∉ S, F z a = 0)
    (hhol : ∀ a : Y, DifferentiableOn ℂ (fun z => F z a) U) :
    DifferentiableOn ℂ (fun z => ∫ a, F z a ∂ν) U := by

  set O : Set Y := ⋃ z ∈ U, {a : Y | F z a ≠ 0} with hO
  have hOopen : IsOpen O := isOpen_nonzero F hF
  have hOS : O ⊆ S := by
    intro a ha
    simp only [hO, mem_iUnion, mem_setOf_eq] at ha
    obtain ⟨z, hz, hne⟩ := ha
    by_contra h
    exact hne (hFS z hz a h)
  have hOfin : ν O < ⊤ := lt_of_le_of_lt (measure_mono hOS) hS.measure_lt_top
  haveI : IsFiniteMeasure (ν.restrict O) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hOm : MeasurableSet O := hOopen.measurableSet

  have hint : ∀ z ∈ U, Integrable (F z) ν := by
    intro z hz
    have hc := continuous_slice F hF hz
    obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
    have hM' : ∀ a, ‖F z a‖ ≤ max M 0 := by
      intro a
      by_cases ha : a ∈ S
      · exact (hM a ha).trans (le_max_left _ _)
      · rw [hFS z hz a ha, norm_zero]; exact le_max_right _ _
    have hIO : IntegrableOn (F z) O ν :=
      Integrable.mono' (integrable_const (max M 0)) hc.aestronglyMeasurable
        (Eventually.of_forall hM')
    refine hIO.integrable_of_forall_notMem_eq_zero fun a ha => ?_
    by_contra hne
    exact ha (mem_iUnion₂.mpr ⟨z, hz, hne⟩)

  intro z₀ hz₀
  obtain ⟨R, hRpos, hRU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  set r : ℝ := R / 4 with hr
  have hrpos : 0 < r := by positivity
  have h2r : closedBall z₀ (2 * r) ⊆ U := by
    refine Subset.trans (closedBall_subset_ball ?_) hRU
    rw [hr]; linarith

  obtain ⟨M₀, hM₀⟩ := ((isCompact_closedBall z₀ (2 * r)).prod hS).exists_bound_of_continuousOn
    (hF.mono (prod_mono h2r (subset_univ _)))
  set M : ℝ := max M₀ 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMb : ∀ z ∈ closedBall z₀ (2 * r), ∀ a, ‖F z a‖ ≤ M := by
    intro z hz a
    by_cases ha : a ∈ S
    · exact (hM₀ (z, a) ⟨hz, ha⟩).trans (le_max_left _ _)
    · rw [hFS z (h2r hz) a ha, norm_zero]; exact hM0

  set F' : ℂ → Y → ℂ := fun z a => deriv (fun z => F z a) z with hF'
  have hderiv : ∀ a, ∀ z ∈ ball z₀ r, HasDerivAt (fun z => F z a) (F' z a) z := by
    intro a z hz
    have hzU : z ∈ U := h2r (by
      have : dist z z₀ < r := hz
      show dist z z₀ ≤ 2 * r
      linarith)
    exact ((hhol a).differentiableAt (hU.mem_nhds hzU)).hasDerivAt
  have hbound : ∀ a, ∀ z ∈ ball z₀ r, ‖F' z a‖ ≤ M / r := by
    intro a z hz
    have hzr : dist z z₀ < r := hz
    have hcl : closedBall z r ⊆ closedBall z₀ (2 * r) := by
      intro w hw
      have : dist w z ≤ r := hw
      show dist w z₀ ≤ 2 * r
      linarith [dist_triangle w z z₀]
    have hdc : DiffContOnCl ℂ (fun z => F z a) (ball z r) := by
      refine DifferentiableOn.diffContOnCl ?_
      rw [closure_ball z hrpos.ne']
      exact (hhol a).mono (hcl.trans h2r)
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hrpos hdc fun w hw => ?_
    exact hMb w (hcl (sphere_subset_closedBall hw)) a

  have hF'O : ∀ z ∈ ball z₀ r, ∀ a ∉ O, F' z a = 0 := by
    intro z hz a ha
    have hzU : z ∈ U := h2r (by
      have : dist z z₀ < r := hz
      show dist z z₀ ≤ 2 * r
      linarith)
    have hzero : ∀ z' ∈ U, F z' a = 0 := by
      intro z' hz'
      by_contra hne
      exact ha (mem_iUnion₂.mpr ⟨z', hz', hne⟩)
    have hev : (fun z => F z a) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
      filter_upwards [hU.mem_nhds hzU] with z' hz' using hzero z' hz'
    show deriv (fun z => F z a) z = 0
    rw [hev.deriv_eq, deriv_const]

  have hF'meas : AEStronglyMeasurable (F' z₀) ν := by
    set t : ℕ → ℂ := fun n => ((r / ((n : ℝ) + 2) : ℝ) : ℂ) with ht
    have htpos : ∀ n : ℕ, 0 < r / ((n : ℝ) + 2) := fun n => div_pos hrpos (by positivity)
    have htne : ∀ n, t n ≠ 0 := fun n => by
      simp only [ht, ne_eq, Complex.ofReal_eq_zero]
      exact (htpos n).ne'
    have htlt : ∀ n, ‖t n‖ < r := fun n => by
      simp only [ht, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (htpos n)]
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    have ht0 : Tendsto t atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall htne⟩
      have h1 : Tendsto (fun n : ℕ => r / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      rw [Complex.ofReal_zero] at h2
      exact h2
    have hlim : Tendsto (fun n a => (t n)⁻¹ • (F (z₀ + t n) a - F z₀ a)) atTop (𝓝 (F' z₀)) := by
      rw [tendsto_pi_nhds]
      intro a
      exact ((hderiv a z₀ (mem_ball_self hrpos)).tendsto_slope_zero).comp ht0
    have hmeas : ∀ n, StronglyMeasurable fun a => (t n)⁻¹ • (F (z₀ + t n) a - F z₀ a) := by
      intro n
      have hzn : z₀ + t n ∈ U := by
        refine h2r ?_
        show dist (z₀ + t n) z₀ ≤ 2 * r
        rw [dist_eq_norm, add_sub_cancel_left]
        linarith [htlt n]
      exact (((continuous_slice F hF hzn).sub (continuous_slice F hF hz₀)).const_smul
        (t n)⁻¹).stronglyMeasurable
    exact (stronglyMeasurable_of_tendsto atTop hmeas hlim).aestronglyMeasurable

  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (F := F) (x₀ := z₀)
    (s := ball z₀ r) (bound := O.indicator fun _ => M / r) (F' := F')
    (ball_mem_nhds z₀ hrpos) ?_ (hint z₀ hz₀) hF'meas ?_ ?_ ?_
  · exact hkey.2.differentiableAt.differentiableWithinAt
  · filter_upwards [hU.mem_nhds hz₀] with z hz
    exact (continuous_slice F hF hz).aestronglyMeasurable
  · refine Eventually.of_forall fun a z hz => ?_
    by_cases ha : a ∈ O
    · rw [indicator_of_mem ha]; exact hbound a z hz
    · rw [indicator_of_notMem ha, hF'O z hz a ha, norm_zero]
  · exact (integrable_indicator_iff hOm).mpr (integrable_const _)
  · exact Eventually.of_forall fun a z hz => hderiv a z hz

end S_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn
end P2MW
export P2MW.S_Complex_differentiableOn_integral_of_continuousOn_of_forall_differentiableOn (solution)
