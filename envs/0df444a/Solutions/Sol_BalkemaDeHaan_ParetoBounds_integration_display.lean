-- Prove2me | solution 1 for BalkemaDeHaan.ParetoBounds.integration_display
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T16:25:43.529768+00:00
-- url     : https://prove2.me/submissions/ac87042d-0c6e-460a-b4e4-9497d3ecd365

import Mathlib

open MeasureTheory ProbabilityTheory


namespace BalkemaDeHaan.ParetoBounds

/-- Basic consequences of the hazard bounds. -/
lemma hazard_basic (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (t₀ α₁ α₂ : ℝ) (hα₁ : 0 < α₁)
    (hdens : ∀ t ≥ t₀, HasDerivWithinAt (cdf μ) (f t) (Set.Ici t₀) t ∧ 0 < f t)
    (hbounds : ∀ t ≥ t₀, α₁ ≤ t * f t / (1 - cdf μ t) ∧ t * f t / (1 - cdf μ t) ≤ α₂)
    (u : ℝ) (hu : t₀ ≤ u) :
    0 < 1 - cdf μ u ∧ 0 < u ∧ α₁ / u ≤ f u / (1 - cdf μ u) ∧ f u / (1 - cdf μ u) ≤ α₂ / u := by
  obtain ⟨_, hf⟩ := hdens u hu
  obtain ⟨h1, h2⟩ := hbounds u hu
  have hF : 0 < 1 - cdf μ u := by
    rcases (sub_nonneg.mpr (cdf_le_one μ u)).lt_or_eq with h | h
    · exact h
    · rw [← h, div_zero] at h1; linarith
  have hu0 : 0 < u := by
    have : 0 < u * f u / (1 - cdf μ u) := lt_of_lt_of_le hα₁ h1
    have : 0 < u * f u := by
      by_contra hc
      push_neg at hc
      have := div_nonpos_of_nonpos_of_nonneg hc hF.le
      linarith
    exact pos_of_mul_pos_left this hf.le
  refine ⟨hF, hu0, ?_, ?_⟩
  · rw [div_le_div_iff₀ hu0 hF]
    rw [le_div_iff₀ hF] at h1
    linarith
  · rw [div_le_div_iff₀ hF hu0]
    rw [div_le_iff₀ hF] at h2
    linarith

theorem integration_display_core (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (t₀ α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hdens : ∀ t ≥ t₀, HasDerivWithinAt (cdf μ) (f t) (Set.Ici t₀) t ∧ 0 < f t)
    (hbounds : ∀ t ≥ t₀, α₁ ≤ t * f t / (1 - cdf μ t) ∧ t * f t / (1 - cdf μ t) ≤ α₂)
    (t : ℝ) (ht : t₀ ≤ t) (x : ℝ) (hx : 0 < x) :
    α₁ * ∫ u in t..(1 + x) * t, 1 / u ≤ ∫ u in t..(1 + x) * t, f u / (1 - cdf μ u) ∧
      ∫ u in t..(1 + x) * t, f u / (1 - cdf μ u) ≤ α₂ * ∫ u in t..(1 + x) * t, 1 / u := by
  have hb := hazard_basic μ f t₀ α₁ α₂ hα₁ hdens hbounds
  have ht0 : 0 < t := (hb t ht).2.1
  have htb : t ≤ (1 + x) * t := by nlinarith
  -- integrability of 1/u
  have hinv : IntervalIntegrable (fun u : ℝ => 1 / u) volume t ((1 + x) * t) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro u hu
    rw [Set.uIcc_of_le htb] at hu
    exact (lt_of_lt_of_le ht0 hu.1).ne'
  -- integrability of f/(1-F)
  have hg : IntervalIntegrable (fun u : ℝ => f u / (1 - cdf μ u)) volume t ((1 + x) * t) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le htb]
    have hmeas : Measurable (fun u : ℝ => derivWithin (cdf μ) (Set.Ici u) u / (1 - cdf μ u)) := by
      apply Measurable.div (measurable_derivWithin_Ici (cdf μ))
      exact measurable_const.sub (monotone_cdf μ).measurable
    have heq : Set.EqOn (fun u : ℝ => derivWithin (cdf μ) (Set.Ici u) u / (1 - cdf μ u))
        (fun u : ℝ => f u / (1 - cdf μ u)) (Set.Ioc t ((1 + x) * t)) := by
      intro u hu
      have hu0 : t₀ < u := lt_of_le_of_lt ht hu.1
      have hd := (hdens u hu0.le).1
      have hd' : HasDerivAt (cdf μ) (f u) u :=
        hd.hasDerivAt (Ici_mem_nhds hu0)
      simp only
      rw [hd'.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici u)]
    refine IntegrableOn.congr_fun ?_ heq measurableSet_Ioc
    apply Measure.integrableOn_of_bounded (M := α₂ / t) measure_Ioc_lt_top.ne
      hmeas.aestronglyMeasurable
    rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun u hu => ?_)
    have hh := heq hu
    simp only at hh
    rw [hh]
    have hu0 : t₀ ≤ u := ht.trans hu.1.le
    obtain ⟨hF, hupos, h1, h2⟩ := hb u hu0
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hdens u hu0).2.le hF.le)]
    refine h2.trans ?_
    exact div_le_div_of_nonneg_left hα₂.le ht0 hu.1.le
  constructor
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on htb (hinv.const_mul _) hg
    intro u hu
    have := (hb u (ht.trans hu.1)).2.2.1
    simpa [div_eq_mul_inv] using this
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on htb hg (hinv.const_mul _)
    intro u hu
    have := (hb u (ht.trans hu.1)).2.2.2
    simpa [div_eq_mul_inv] using this

end BalkemaDeHaan.ParetoBounds

open BalkemaDeHaan.ParetoBounds


theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ → ℝ)
    (t₀ α₁ α₂ : ℝ) (hα₁ : 0 < α₁) (hα₂ : 0 < α₂)
    (hdens : ∀ t ≥ t₀, HasDerivWithinAt (cdf μ) (f t) (Set.Ici t₀) t ∧ 0 < f t)
    (hbounds : ∀ t ≥ t₀, α₁ ≤ t * f t / (1 - cdf μ t) ∧ t * f t / (1 - cdf μ t) ≤ α₂)
    (t : ℝ) (ht : t₀ ≤ t) (x : ℝ) (hx : 0 < x) :
    α₁ * ∫ u in t..(1 + x) * t, 1 / u ≤ ∫ u in t..(1 + x) * t, f u / (1 - cdf μ u) ∧
      ∫ u in t..(1 + x) * t, f u / (1 - cdf μ u) ≤ α₂ * ∫ u in t..(1 + x) * t, 1 / u := by
  exact integration_display_core μ f t₀ α₁ α₂ hα₁ hα₂ hdens hbounds t ht x hx
