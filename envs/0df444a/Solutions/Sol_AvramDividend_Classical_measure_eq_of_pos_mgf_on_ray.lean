-- Prove2me | solution 1 for AvramDividend.Classical.measure_eq_of_pos_mgf_on_ray
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:15:41.050655+00:00
-- url     : https://prove2.me/submissions/360f9b69-7b51-461a-8a54-0baf4a4e11dd

import Mathlib

open MeasureTheory ProbabilityTheory Set Filter Topology Complex

namespace S189MG

/-- integral against the tilted measure -/
lemma S189MG_int (μ : Measure ℝ) (g : ℝ → ℝ) :
    ∫ x, g x ∂(μ.withDensity (fun x => ENNReal.ofReal (Real.exp x)))
      = ∫ x, Real.exp x * g x ∂μ := by
  have hm : Measurable (fun x : ℝ => (Real.exp x).toNNReal) := by fun_prop
  have := integral_withDensity_eq_integral_smul hm g (μ := μ)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le] at this
  exact this

lemma S189MG_intble (μ : Measure ℝ) (g : ℝ → ℝ) :
    Integrable g (μ.withDensity (fun x => ENNReal.ofReal (Real.exp x)))
      ↔ Integrable (fun x => Real.exp x * g x) μ := by
  have hm : Measurable (fun x : ℝ => (Real.exp x).toNNReal) := by fun_prop
  have := integrable_withDensity_iff_integrable_smul hm (g := g) (μ := μ)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le] at this
  exact this

lemma S189MG_finite (μ : Measure ℝ) (h : Integrable (fun x : ℝ => Real.exp x) μ) :
    IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (Real.exp x))) :=
  isFiniteMeasure_withDensity_ofReal h.2

lemma S189MG_recover (μ : Measure ℝ) :
    (μ.withDensity (fun x => ENNReal.ofReal (Real.exp x))).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-x))) = μ := by
  rw [← withDensity_mul _ (by fun_prop) (by fun_prop)]
  have : ((fun x : ℝ => ENNReal.ofReal (Real.exp x)) * fun x => ENNReal.ofReal (Real.exp (-x)))
      = 1 := by
    funext x
    simp only [Pi.mul_apply, Pi.one_apply]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  rw [this, withDensity_one]

lemma S189MG_intble_t (μ : Measure ℝ)
    (hμ : ∀ s : ℝ, 0 < s → Integrable (fun x : ℝ => Real.exp (s * x)) μ) (t : ℝ) (ht : -1 < t) :
    Integrable (fun x : ℝ => Real.exp (t * x))
      (μ.withDensity (fun x => ENNReal.ofReal (Real.exp x))) := by
  rw [S189MG_intble]
  have := hμ (t + 1) (by linarith)
  refine this.congr (ae_of_all _ fun x => ?_)
  simp only
  rw [← Real.exp_add]; ring_nf

lemma S189MG_mgf_t (μ : Measure ℝ) (t : ℝ) :
    ∫ x, Real.exp (t * x) ∂(μ.withDensity (fun x => ENNReal.ofReal (Real.exp x)))
      = ∫ x, Real.exp ((t + 1) * x) ∂μ := by
  rw [S189MG_int]
  congr 1; funext x
  rw [← Real.exp_add]; ring_nf

lemma S189MG_strip (μ : Measure ℝ)
    (hμ : ∀ s : ℝ, 0 < s → Integrable (fun x : ℝ => Real.exp (s * x)) μ) :
    AnalyticOnNhd ℂ (complexMGF id (μ.withDensity (fun x => ENNReal.ofReal (Real.exp x))))
      {z : ℂ | -1 < z.re} := by
  refine analyticOnNhd_complexMGF.mono ?_
  intro z hz
  simp only [Set.mem_ofPred_eq] at hz ⊢
  have : Ioi (-1 : ℝ) ⊆ interior (integrableExpSet id
      (μ.withDensity (fun x => ENNReal.ofReal (Real.exp x)))) := by
    refine isOpen_Ioi.subset_interior_iff.mpr ?_
    intro t ht
    exact S189MG_intble_t μ hμ t ht
  exact this hz

set_option backward.isDefEq.respectTransparency.types false in
lemma S189MG_ext {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ w : ℝ, complexMGF id μ (w * I) = complexMGF id ν (w * I)) : μ = ν := by
  have inner_ne_zero (x : ℝ) (h : x ≠ 0) : innerₗ ℝ x ≠ 0 :=
    DFunLike.ne_iff.mpr ⟨x, inner_self_ne_zero.mpr h⟩
  apply MeasureTheory.ext_of_integral_char_eq Real.continuous_probChar Real.probChar_ne_one inner_ne_zero
    continuous_inner (fun w ↦ ?_)
  specialize h (Multiplicative.toAdd w)
  simp_rw [complexMGF, mul_assoc, mul_comm I, ← mul_assoc] at h
  simp only [BoundedContinuousFunction.char_apply, innerₗ_apply_apply,
    RCLike.inner_apply, conj_trivial, Real.probChar_apply, ofReal_mul]
  exact h

end S189MG

open S189MG in
theorem solution
    {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : ∀ s : ℝ, 0 < s → Integrable (fun x : ℝ => Real.exp (s * x)) μ)
    (hν : ∀ s : ℝ, 0 < s → Integrable (fun x : ℝ => Real.exp (s * x)) ν)
    (hm : ∀ s : ℝ, 0 < s →
      (∫ x, Real.exp (s * x) ∂μ) = ∫ x, Real.exp (s * x) ∂ν) : μ = ν := by
  set μ₁ := μ.withDensity (fun x => ENNReal.ofReal (Real.exp x)) with hμ₁
  set ν₁ := ν.withDensity (fun x => ENNReal.ofReal (Real.exp x)) with hν₁
  have : IsFiniteMeasure μ₁ := S189MG_finite μ (by simpa using hμ 1 one_pos)
  have : IsFiniteMeasure ν₁ := S189MG_finite ν (by simpa using hν 1 one_pos)
  have hreal : ∀ t : ℝ, -1 < t → complexMGF id μ₁ t = complexMGF id ν₁ t := by
    intro t ht
    rw [complexMGF_ofReal, complexMGF_ofReal]
    congr 1
    simp only [mgf, id]
    rw [hμ₁, hν₁, S189MG_mgf_t, S189MG_mgf_t, hm _ (by linarith)]
  have hconn : IsPreconnected {z : ℂ | -1 < z.re} :=
    (convex_halfSpace_re_gt (-1)).isPreconnected
  have heq : EqOn (complexMGF id μ₁) (complexMGF id ν₁) {z : ℂ | -1 < z.re} := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq (S189MG_strip μ hμ)
      (S189MG_strip ν hν) hconn (z₀ := (0 : ℂ)) (by simp) ?_
    have hev : ∀ᶠ y : ℝ in 𝓝[≠] (0:ℝ), complexMGF id μ₁ y = complexMGF id ν₁ y := by
      have : ∀ᶠ y : ℝ in 𝓝 (0:ℝ), -1 < y := Ioi_mem_nhds (by norm_num)
      exact (eventually_nhdsWithin_of_eventually_nhds this).mono fun y hy => hreal y hy
    have h_real := hev.frequently
    rw [frequently_iff_seq_forall] at h_real ⊢
    obtain ⟨xs, hx_tendsto, hx_eq⟩ := h_real
    refine ⟨fun n ↦ xs n, ?_, fun n ↦ ?_⟩
    · rw [tendsto_nhdsWithin_iff] at hx_tendsto ⊢
      constructor
      · have := (continuous_ofReal.tendsto 0).comp hx_tendsto.1
        exact this
      · simpa using hx_tendsto.2
    · simp [hx_eq]
  have h1 : μ₁ = ν₁ := S189MG_ext fun w => heq (by simp)
  rw [← S189MG_recover μ, ← S189MG_recover ν, ← hμ₁, ← hν₁, h1]
