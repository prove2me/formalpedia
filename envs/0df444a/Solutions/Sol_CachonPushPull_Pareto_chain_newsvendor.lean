-- Prove2me | solution 1 for CachonPushPull.Pareto.chain_newsvendor
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T08:06:26.363806+00:00
-- url     : https://prove2.me/submissions/cc17f6ec-372c-4903-b757-1705c4a09c4e

import Mathlib
import Definitions.Def_CachonPushPull_Pareto_Model

namespace CachonPushPull.Pareto

open MeasureTheory ProbabilityTheory

lemma aux_cnv_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) : ∀ x ≤ 0, cdf μ x = 0 := fun x hx =>
  le_antisymm (hD.cdf_zero ▸ (cdf μ).mono hx) (cdf_nonneg μ x)

lemma aux_cnv_cont (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) : Continuous (cdf μ) := by
  have hle := aux_cnv_zero μ f hD
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy x 0 with h | rfl | h
  · have : (cdf μ : ℝ → ℝ) =ᶠ[nhds x] fun _ => (0:ℝ) := by
      filter_upwards [Iio_mem_nhds h] with y hy using hle y hy.le
    exact continuousAt_const.congr this.symm
  · rw [continuousAt_iff_continuous_left_right]
    refine ⟨?_, (cdf μ).right_continuous 0⟩
    have : ContinuousWithinAt (fun _ => (0:ℝ)) (Set.Iic (0:ℝ)) 0 := continuousWithinAt_const
    exact this.congr (fun (y : ℝ) (hy : y ∈ Set.Iic (0:ℝ)) => hle y (Set.mem_Iic.1 hy))
      (hle 0 le_rfl)
  · exact (hD.hasDerivAt x h).continuousAt

lemma aux_cnv_deriv (μ : Measure ℝ) (hc : Continuous (cdf μ)) (p c v q : ℝ) :
    HasDerivAt (chainProfit μ p c v) ((p - v) * (1 - cdf μ q) - (c - v)) q := by
  have h1 : HasDerivAt (fun q => ∫ x in (0:ℝ)..q, cdf μ x) (cdf μ q) q :=
    (hc.integral_hasStrictDerivAt 0 q).hasDerivAt
  have h2 : HasDerivAt (S μ) (1 - cdf μ q) q := by
    unfold S
    exact (hasDerivAt_id' q).sub h1
  have h3 : HasDerivAt (fun y => (p - v) * S μ y - (c - v) * y)
      ((p - v) * (1 - cdf μ q) - (c - v) * 1) q :=
    (h2.const_mul (p - v)).sub ((hasDerivAt_id' q).const_mul (c - v))
  have he : chainProfit μ p c v = fun q => (p - v) * S μ q - (c - v) * q := rfl
  rw [he]
  exact h3.congr_deriv (by ring)

end CachonPushPull.Pareto

open CachonPushPull.Pareto
open MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p) :
    ConcaveOn ℝ (Set.Ici 0) (chainProfit μ p c v) ∧
    (∃! qo : ℝ, cdf μ qo = (p - c) / (p - v)) ∧
    ∀ qo : ℝ, cdf μ qo = (p - c) / (p - v) →
      0 < qo ∧ IsMaxOn (chainProfit μ p c v) (Set.Ici 0) qo ∧
      StrictMonoOn (chainProfit μ p c v) (Set.Icc 0 qo) := by
  have hc := aux_cnv_cont μ f hD
  have hle := aux_cnv_zero μ f hD
  have hpv : 0 < p - v := by linarith
  have hα0 : 0 < (p - c) / (p - v) := div_pos (by linarith) hpv
  have hα1 : (p - c) / (p - v) < 1 := by rw [div_lt_one hpv]; linarith
  have hderiv : ∀ q, HasDerivAt (chainProfit μ p c v)
      ((p - v) * (1 - cdf μ q) - (c - v)) q := aux_cnv_deriv μ hc p c v
  have hdf : deriv (chainProfit μ p c v) = fun q => (p - v) * (1 - cdf μ q) - (c - v) :=
    funext fun q => (hderiv q).deriv
  have hdiff : Differentiable ℝ (chainProfit μ p c v) := fun q => (hderiv q).differentiableAt
  have hkey : ∀ q, (p - v) * (1 - cdf μ q) - (c - v) = (p - v) * ((p - c) / (p - v) - cdf μ q) := by
    intro q; field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · apply AntitoneOn.concaveOn_of_deriv (convex_Ici 0) hdiff.continuous.continuousOn
      hdiff.differentiableOn
    rw [hdf]
    intro x _ y _ hxy
    have := (cdf μ).mono hxy
    simp only
    nlinarith
  · obtain ⟨b, hb⟩ : ∃ b, (p - c) / (p - v) < cdf μ b :=
      ((tendsto_cdf_atTop μ).eventually (lt_mem_nhds hα1)).exists
    have hb0 : 0 ≤ b := by
      by_contra h; push Not at h; rw [hle b h.le] at hb; linarith
    obtain ⟨qo, hqo, hFq⟩ := intermediate_value_Icc hb0 hc.continuousOn
      ⟨by rw [hD.cdf_zero]; exact hα0.le, hb.le⟩
    refine ⟨qo, hFq, fun y (hy : cdf μ y = (p - c) / (p - v)) => ?_⟩
    have hy0 : 0 ≤ y := by
      by_contra h; push Not at h; rw [hle y h.le] at hy; linarith
    exact hD.strictMonoOn.injOn (Set.mem_Ici.2 hy0) (Set.mem_Ici.2 hqo.1) (hy.trans hFq.symm)
  · intro qo hqo
    have hq0 : 0 < qo := by
      by_contra h; push Not at h; rw [hle qo h] at hqo; linarith
    have hsm : StrictMonoOn (chainProfit μ p c v) (Set.Icc 0 qo) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc 0 qo) hdiff.continuous.continuousOn
      intro x hx
      rw [interior_Icc] at hx
      rw [hdf]; simp only; rw [hkey]
      have : cdf μ x < cdf μ qo :=
        hD.strictMonoOn (Set.mem_Ici.2 hx.1.le) (Set.mem_Ici.2 hq0.le) hx.2
      apply mul_pos hpv; linarith
    refine ⟨hq0, ?_, hsm⟩
    have hanti : AntitoneOn (chainProfit μ p c v) (Set.Ici qo) := by
      apply antitoneOn_of_deriv_nonpos (convex_Ici qo) hdiff.continuous.continuousOn
        hdiff.differentiableOn
      intro x hx
      rw [interior_Ici] at hx
      rw [hdf]; simp only; rw [hkey]
      have : cdf μ qo ≤ cdf μ x := (cdf μ).mono (le_of_lt hx)
      apply mul_nonpos_of_nonneg_of_nonpos hpv.le; linarith
    rw [isMaxOn_iff]
    intro q hq
    rcases le_total q qo with h | h
    · exact hsm.monotoneOn ⟨hq, h⟩ ⟨hq0.le, le_rfl⟩ h
    · exact hanti (Set.mem_Ici.2 le_rfl) h h
