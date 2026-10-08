-- Prove2me | solution 1 for CachonPushPull.ShippingCost.supplier_profit_deriv_limit
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-06T02:24:51.79762+00:00
-- url     : https://prove2.me/submissions/32de48e3-fbca-4a93-a24d-1f729492046e

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


theorem spdl_deriv (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (c v : ℝ)
    (τ : ℝ) (w₂ : ℝ) (yr : ℝ → ℝ)
    (hyr : ∀ w : ℝ, w ∈ Set.Ioo v w₂ → 0 ≤ yr w ∧ cdf μ (yr w) = (w₂ - w) / (w₂ - v))
    (q w₁ : ℝ) (hw₁ : w₁ ∈ Set.Ioo v w₂) (hf : 0 < f (yr w₁)) :
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

theorem spdl_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (c v : ℝ)
    (τ : ℝ) (hτ : 0 < τ) (w₂ : ℝ) (hvw₂ : v < w₂) (yr : ℝ → ℝ)
    (hyr : ∀ w : ℝ, w ∈ Set.Ioo v w₂ → 0 ≤ yr w ∧ cdf μ (yr w) = (w₂ - w) / (w₂ - v))
    (q : ℝ) :
    Tendsto yr (𝓝[<] w₂) (𝓝 0) ∧
    ∀ f₀ : ℝ, 0 < f₀ → Tendsto f (𝓝[>] 0) (𝓝 f₀) →
      Tendsto (fun w₁ : ℝ => deriv (fun w : ℝ => supplierProfit μ c v τ w w₂ (yr w) q) w₁)
          (𝓝[<] w₂) (𝓝 (-τ / ((w₂ - v) * f₀))) ∧
        -τ / ((w₂ - v) * f₀) < 0 := by
  have hwv : 0 < w₂ - v := by linarith
  have hpos : ∀ w ∈ Set.Ioo v w₂, 0 < yr w := by
    intro w hw
    obtain ⟨hy0, hval⟩ := hyr w hw
    rcases hy0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, hD.cdf_zero] at hval
      have : 0 < (w₂ - w) / (w₂ - v) := div_pos (by linarith [hw.2]) hwv
      linarith
  have hev : ∀ᶠ w in 𝓝[<] w₂, w ∈ Set.Ioo v w₂ := Ioo_mem_nhdsLT hvw₂
  have hcont : Continuous (fun w : ℝ => (w₂ - w) / (w₂ - v)) :=
    (continuous_const.sub continuous_id).div_const _
  have hlim0 : Tendsto (fun w : ℝ => (w₂ - w) / (w₂ - v)) (𝓝[<] w₂) (𝓝 0) := by
    have := (hcont.tendsto w₂).mono_left (nhdsWithin_le_nhds (s := Set.Iio w₂))
    simpa using this
  have h1 : Tendsto yr (𝓝[<] w₂) (𝓝 0) := by
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · filter_upwards [hev] with w hw
      exact lt_of_lt_of_le ha (hyr w hw).1
    · have hb0 : 0 < cdf μ b := by
        have := hD.strictMonoOn (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hb.le) hb
        rwa [hD.cdf_zero] at this
      filter_upwards [hev, hlim0.eventually (gt_mem_nhds hb0)] with w hw h2w
      rw [← (hyr w hw).2] at h2w
      by_contra hcon
      push_neg at hcon
      exact absurd (monotone_cdf μ hcon) (not_le.2 h2w)
  refine ⟨h1, fun f₀ hf₀ hf => ?_⟩
  have hden : 0 < (w₂ - v) * f₀ := mul_pos hwv hf₀
  refine ⟨?_, by
    have : 0 < τ / ((w₂ - v) * f₀) := div_pos hτ hden
    rw [neg_div]; linarith⟩
  have h1' : Tendsto yr (𝓝[<] w₂) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨h1, by
      filter_upwards [hev] with w hw
      exact hpos w hw⟩
  have hfy : Tendsto (fun w => f (yr w)) (𝓝[<] w₂) (𝓝 f₀) := hf.comp h1'
  have hfpos : ∀ᶠ w in 𝓝[<] w₂, 0 < f (yr w) := hfy.eventually (lt_mem_nhds hf₀)
  have hE : (fun w₁ : ℝ => deriv (fun w : ℝ => supplierProfit μ c v τ w w₂ (yr w) q) w₁)
      =ᶠ[𝓝[<] w₂] (fun w₁ => yr w₁ - ((w₁ - v) - (w₂ - τ - v) * (1 - (w₂ - w₁) / (w₂ - v)))
        / ((w₂ - v) * f (yr w₁))) := by
    filter_upwards [hev, hfpos] with w hw hfw
    rw [(spdl_deriv μ f hD c v τ w₂ yr hyr q w hw hfw).deriv, (hyr w hw).2]
  refine Tendsto.congr' hE.symm ?_
  have hnum : Tendsto (fun w₁ : ℝ => (w₁ - v) - (w₂ - τ - v) * (1 - (w₂ - w₁) / (w₂ - v)))
      (𝓝[<] w₂) (𝓝 τ) := by
    have hc2 : Continuous (fun w₁ : ℝ => (w₁ - v) - (w₂ - τ - v) * (1 - (w₂ - w₁) / (w₂ - v))) := by
      fun_prop
    have := (hc2.tendsto w₂).mono_left (nhdsWithin_le_nhds (s := Set.Iio w₂))
    convert this using 2
    simp
  have hd : Tendsto (fun w₁ => (w₂ - v) * f (yr w₁)) (𝓝[<] w₂) (𝓝 ((w₂ - v) * f₀)) :=
    hfy.const_mul _
  have := h1.sub (hnum.div hd hden.ne')
  have heq : -τ / ((w₂ - v) * f₀) = 0 - τ / ((w₂ - v) * f₀) := by ring
  rw [heq]
  exact this

end CachonPushPull.ShippingCost

open CachonPushPull.ShippingCost
open MeasureTheory ProbabilityTheory Filter Topology

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (hD : DemandModel μ f) (p c v : ℝ) (hvc : v < c) (hcp : c < p)
    (τ : ℝ) (hτ : 0 < τ) (w₂ : ℝ) (hvw₂ : v < w₂) (hw₂p : w₂ ≤ p) (yr : ℝ → ℝ)
    (hyr : ∀ w : ℝ, w ∈ Set.Ioo v w₂ → 0 ≤ yr w ∧ cdf μ (yr w) = (w₂ - w) / (w₂ - v))
    (q : ℝ) :
    Tendsto yr (𝓝[<] w₂) (𝓝 0) ∧
    ∀ f₀ : ℝ, 0 < f₀ → Tendsto f (𝓝[>] 0) (𝓝 f₀) →
      Tendsto (fun w₁ : ℝ => deriv (fun w : ℝ => supplierProfit μ c v τ w w₂ (yr w) q) w₁)
          (𝓝[<] w₂) (𝓝 (-τ / ((w₂ - v) * f₀))) ∧
        -τ / ((w₂ - v) * f₀) < 0 := by
  exact spdl_core μ f hD c v τ hτ w₂ hvw₂ yr hyr q
