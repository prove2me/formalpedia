-- Prove2me | solution 1 for CachonPushPull.ShippingCost.supplier_profit_deriv
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:00:48.009745+00:00
-- url     : https://prove2.me/submissions/d288d71c-5ca1-48b3-84d3-3e2d9d14418a

import Mathlib
import Definitions.Def_CachonPushPull_ShippingCost_Game

namespace CachonPushPull.ShippingCost

open MeasureTheory ProbabilityTheory Filter Topology

theorem aux_spd_S_deriv (μ : Measure ℝ) [IsProbabilityMeasure μ] (y : ℝ)
    (hc : ContinuousAt (cdf μ) y) : HasDerivAt (S μ) (1 - cdf μ y) y := by
  have h1 : HasDerivAt (fun u => ∫ x in (0:ℝ)..u, cdf μ x) (cdf μ y) y :=
    intervalIntegral.integral_hasDerivAt_right ((monotone_cdf μ).intervalIntegrable)
      ((monotone_cdf μ).measurable.stronglyMeasurable.stronglyMeasurableAtFilter) hc
  show HasDerivAt (fun q => q - ∫ x in (0:ℝ)..q, cdf μ x) (1 - cdf μ y) y
  exact (hasDerivAt_id y).sub h1

theorem aux_spd_yr_cont (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (v w₂ : ℝ) (yr : ℝ → ℝ)
    (hyr : ∀ w : ℝ, w ∈ Set.Ioo v w₂ → 0 ≤ yr w ∧ cdf μ (yr w) = (w₂ - w) / (w₂ - v))
    (w₁ : ℝ) (hw₁ : w₁ ∈ Set.Ioo v w₂) (hpos : 0 < yr w₁) : ContinuousAt yr w₁ := by
  have hev : ∀ᶠ w in 𝓝 w₁, w ∈ Set.Ioo v w₂ := Ioo_mem_nhds hw₁.1 hw₁.2
  have hcont : Continuous (fun w : ℝ => (w₂ - w) / (w₂ - v)) :=
    (continuous_const.sub continuous_id).div_const _
  have hval := (hyr w₁ hw₁).2
  rw [ContinuousAt, tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · set a' := max a 0 with ha'def
    have ha' : a' < yr w₁ := max_lt ha hpos
    have hlt : cdf μ a' < cdf μ (yr w₁) :=
      hD.strictMonoOn (Set.mem_Ici.2 (le_max_right _ _)) (Set.mem_Ici.2 hpos.le) ha'
    rw [hval] at hlt
    have h2 : ∀ᶠ w in 𝓝 w₁, cdf μ a' < (w₂ - w) / (w₂ - v) :=
      (hcont.tendsto w₁).eventually (lt_mem_nhds hlt)
    filter_upwards [hev, h2] with w hw h2w
    rw [← (hyr w hw).2] at h2w
    have : a' < yr w := by
      by_contra hcon
      push Not at hcon
      exact absurd (monotone_cdf μ hcon) (not_le.2 h2w)
    exact lt_of_le_of_lt (le_max_left _ _) this
  · have hlt : cdf μ (yr w₁) < cdf μ b :=
      hD.strictMonoOn (Set.mem_Ici.2 hpos.le) (Set.mem_Ici.2 (hpos.le.trans hb.le)) hb
    rw [hval] at hlt
    have h2 : ∀ᶠ w in 𝓝 w₁, (w₂ - w) / (w₂ - v) < cdf μ b :=
      (hcont.tendsto w₁).eventually (gt_mem_nhds hlt)
    filter_upwards [hev, h2] with w hw h2w
    rw [← (hyr w hw).2] at h2w
    by_contra hcon
    push Not at hcon
    exact absurd (monotone_cdf μ hcon) (not_le.2 h2w)

end CachonPushPull.ShippingCost

open CachonPushPull.ShippingCost
open MeasureTheory ProbabilityTheory

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (τ : ℝ) (hτ : 0 < τ) (w₂ : ℝ) (hw₂p : w₂ ≤ p) (yr : ℝ → ℝ)
    (hyr : ∀ w : ℝ, w ∈ Set.Ioo v w₂ → 0 ≤ yr w ∧ cdf μ (yr w) = (w₂ - w) / (w₂ - v))
    (q w₁ : ℝ) (hw₁ : w₁ ∈ Set.Ioo v w₂) (hf : 0 < f (yr w₁)) :
    HasDerivAt yr (-((w₂ - v) * f (yr w₁))⁻¹) w₁ ∧
    HasDerivAt (fun w : ℝ => supplierProfit μ c v τ w w₂ (yr w) q)
      (yr w₁ - ((w₁ - v) - (w₂ - τ - v) * (1 - cdf μ (yr w₁))) / ((w₂ - v) * f (yr w₁)))
      w₁ := by
  obtain ⟨hy0, hval⟩ := hyr w₁ hw₁
  have hwv : 0 < w₂ - v := by linarith [hw₁.1, hw₁.2]
  have hpos : 0 < yr w₁ := by
    rcases hy0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, hD.cdf_zero] at hval
      have : 0 < (w₂ - w₁) / (w₂ - v) := div_pos (by linarith [hw₁.2]) hwv
      linarith
  have hcont := aux_spd_yr_cont μ f hD v w₂ yr hyr w₁ hw₁ hpos
  have hF : HasDerivAt (cdf μ) (f (yr w₁)) (yr w₁) := hD.hasDerivAt _ hpos
  have hG : HasDerivAt (fun y => w₂ - (w₂ - v) * cdf μ y) (-((w₂ - v) * f (yr w₁))) (yr w₁) :=
    (hF.const_mul (w₂ - v)).const_sub w₂
  have hne : -((w₂ - v) * f (yr w₁)) ≠ 0 := by
    have := mul_pos hwv hf
    linarith
  have hloc : ∀ᶠ w in nhds w₁, (fun y => w₂ - (w₂ - v) * cdf μ y) (yr w) = w := by
    filter_upwards [Ioo_mem_nhds hw₁.1 hw₁.2] with w hw
    rw [(hyr w hw).2]
    field_simp
    ring
  have hyd : HasDerivAt yr (-((w₂ - v) * f (yr w₁)))⁻¹ w₁ :=
    HasDerivAt.of_local_left_inverse hcont hG hne hloc
  have hyd' : HasDerivAt yr (-((w₂ - v) * f (yr w₁))⁻¹) w₁ := by
    rwa [inv_neg] at hyd
  refine ⟨hyd', ?_⟩
  have hS : HasDerivAt (S μ) (1 - cdf μ (yr w₁)) (yr w₁) :=
    aux_spd_S_deriv μ _ hF.continuousAt
  have hSc : HasDerivAt (fun w => S μ (yr w))
      ((1 - cdf μ (yr w₁)) * (-((w₂ - v) * f (yr w₁))⁻¹)) w₁ :=
    hS.comp w₁ hyd'
  have hmain := ((((hasDerivAt_id w₁).sub_const v).mul hyd').add
    (((hasDerivAt_const w₁ (S μ q)).sub hSc).const_mul (w₂ - τ - v))).sub_const ((c - v) * q)
  refine HasDerivAt.congr_deriv hmain ?_
  simp only [id]
  field_simp
  ring
