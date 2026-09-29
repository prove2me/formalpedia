-- Prove2me | solution 2 for EthierKurtz.kmt_affine_standardize
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T06:40:38.703065+00:00
-- url     : https://prove2.me/submissions/f98e280c-e9c4-4277-a16f-d9b113b0d12f

import Mathlib

open MeasureTheory ProbabilityTheory in
private lemma p2m37e3_exists_dirac
    (mu : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real)))
    (hvar : variance (fun x : Real => x) (mu : Measure Real) = 0) :
    Exists fun m : Real => Measure.map (fun _ : Real => m) (mu : Measure Real) = (mu : Measure Real) := by
  obtain ⟨a0, ha0, hint⟩ := hexp
  have hpos : Integrable (fun x : Real => Real.exp (a0 * x)) (mu : Measure Real) :=
    hint a0 (by rw [abs_of_pos ha0])
  have hneg : Integrable (fun x : Real => Real.exp (-a0 * x)) (mu : Measure Real) :=
    hint (-a0) (by rw [abs_neg, abs_of_pos ha0])
  have hsq : Integrable (fun x : Real => x ^ 2) (mu : Measure Real) :=
    integrable_pow_of_integrable_exp_mul (X := fun x : Real => x) ha0.ne' hpos hneg 2
  have hLp : MemLp (fun x : Real => x) 2 (mu : Measure Real) :=
    (memLp_two_iff_integrable_sq measurable_id.aestronglyMeasurable).2 hsq
  have hlt : evariance (fun x : Real => x) (mu : Measure Real) < ⊤ :=
    (evariance_lt_top_iff_memLp measurable_id.aestronglyMeasurable).2 hLp
  have hev : evariance (fun x : Real => x) (mu : Measure Real) = 0 := by
    have h0 : (evariance (fun x : Real => x) (mu : Measure Real)).toReal = 0 := hvar
    rcases ENNReal.toReal_eq_zero_iff _ |>.1 h0 with h | h
    · exact h
    · exact absurd h hlt.ne
  have hae := (evariance_eq_zero_iff (X := fun x : Real => x) measurable_id.aemeasurable).1 hev
  refine ⟨MeasureTheory.integral (mu : Measure Real) (fun x : Real => x), ?_⟩
  exact (Measure.map_congr hae.symm).trans Measure.map_id'

open MeasureTheory ProbabilityTheory in
private lemma d4d73198_zero_case
    (mu : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real)))
    (hvar : variance (fun x : Real => x) (mu : Measure Real) = 0) :
    Exists fun (nu : ProbabilityMeasure Real) => Exists fun m : Real => Exists fun sigma : Real =>
      And (0 <= sigma) (And (Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
      (And (MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
      (And (variance (fun y : Real => y) (nu : Measure Real) = 1)
      (Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
        Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)))))) := by
  obtain ⟨m, hm⟩ := p2m37e3_exists_dirac mu hexp hvar
  refine ⟨⟨gaussianReal 0 1, inferInstance⟩, m, 0, le_refl 0, ?_, ?_, ?_, 1, one_pos, fun a _ => ?_⟩
  · have h1 : Measure.map (fun y : Real => m + 0 * y) (gaussianReal 0 1)
        = Measure.map (fun _ : Real => m) (gaussianReal 0 1) := by
      congr 1
      funext y
      simp
    change Measure.map (fun y : Real => m + 0 * y) (gaussianReal 0 1) = (mu : Measure Real)
    rw [h1, Measure.map_const, ← hm, Measure.map_const]
    simp
  · exact integral_id_gaussianReal
  · simp
  · exact integrable_exp_mul_gaussianReal a

open MeasureTheory ProbabilityTheory in
private lemma d15a1b08_standardize
    (mu : ProbabilityMeasure Real)
    (hvar : 0 < variance (fun x : Real => x) (mu : Measure Real)) :
    Exists fun (nu : ProbabilityMeasure Real) => Exists fun m : Real => Exists fun sigma : Real =>
      And (0 < sigma) (And (Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
      (And (MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
      (variance (fun y : Real => y) (nu : Measure Real) = 1))) := by
  set V : Real := variance (fun x : Real => x) (mu : Measure Real) with hV
  set m : Real := MeasureTheory.integral (mu : Measure Real) (fun y : Real => y) with hm
  set s : Real := Real.sqrt V with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr hvar
  have hsne : s ≠ 0 := hspos.ne'
  have hs2 : s ^ 2 = V := Real.sq_sqrt hvar.le
  have hLp : MemLp (fun y : Real => y) 2 (mu : Measure Real) :=
    memLp_two_of_variance_ne_zero measurable_id.aestronglyMeasurable hvar.ne'
  have hint : Integrable (fun y : Real => y) (mu : Measure Real) :=
    hLp.integrable one_le_two
  let f : Real → Real := fun x => s⁻¹ * (x - m)
  have hf : Measurable f := by fun_prop
  let nu : ProbabilityMeasure Real := mu.map hf.aemeasurable
  have hnu : (nu : Measure Real) = Measure.map f (mu : Measure Real) :=
    ProbabilityMeasure.toMeasure_map mu hf.aemeasurable
  have hg : Measurable (fun y : Real => m + s * y) := by fun_prop
  refine ⟨nu, m, s, hspos, ?_, ?_, ?_⟩
  · rw [hnu, Measure.map_map hg hf]
    have : ((fun y : Real => m + s * y) ∘ f) = id := by
      funext x
      simp only [Function.comp, f, id]
      field_simp
      ring
    rw [this, Measure.map_id]
  · rw [hnu, integral_map hf.aemeasurable (by fun_prop)]
    simp only [f]
    rw [integral_const_mul, integral_sub hint (integrable_const m), integral_const]
    simp [hm]
  · rw [hnu]
    have h1 := variance_id_map (μ := (mu : Measure Real)) hf.aemeasurable
    have h2 := variance_const_mul s⁻¹ (fun x : Real => x - m) (mu : Measure Real)
    have h3 := variance_sub_const (μ := (mu : Measure Real))
      (X := fun x : Real => x) measurable_id.aestronglyMeasurable m
    calc variance (fun y : Real => y) (Measure.map f (mu : Measure Real))
        = variance f (mu : Measure Real) := h1
      _ = s⁻¹ ^ 2 * variance (fun x : Real => x - m) (mu : Measure Real) := h2
      _ = s⁻¹ ^ 2 * V := by rw [h3]
      _ = 1 := by rw [← hs2]; field_simp

open MeasureTheory ProbabilityTheory in
private lemma d15a1b08_exp_transport
    (mu nu : ProbabilityMeasure Real) (m sigma : Real)
    (hsigma : 0 < sigma)
    (hmap : Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real))) :
    Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)) := by
  obtain ⟨a0, ha0, hint⟩ := hexp
  refine ⟨a0 * sigma, mul_pos ha0 hsigma, fun b hb => ?_⟩
  have hmeas : Measurable (fun y : Real => m + sigma * y) := by fun_prop
  have hab : |b / sigma| ≤ a0 := by
    rw [abs_div, abs_of_pos hsigma, div_le_iff₀ hsigma]
    exact hb
  have h1 := hint (b / sigma) hab
  rw [← hmap, integrable_map_measure (by fun_prop) hmeas.aemeasurable] at h1
  have h2 := h1.const_mul (Real.exp (-(b / sigma * m)))
  refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply]
  rw [← Real.exp_add]
  congr 1
  field_simp
  ring

open MeasureTheory ProbabilityTheory in
private lemma d4d73198_pos_case
    (mu : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (mu : Measure Real)))
    (hvar : 0 < variance (fun x : Real => x) (mu : Measure Real)) :
    Exists fun (nu : ProbabilityMeasure Real) => Exists fun m : Real => Exists fun sigma : Real =>
      And (0 <= sigma) (And (Measure.map (fun y : Real => m + sigma * y) (nu : Measure Real) = (mu : Measure Real))
      (And (MeasureTheory.integral (nu : Measure Real) (fun y : Real => y) = 0)
      (And (variance (fun y : Real => y) (nu : Measure Real) = 1)
      (Exists fun a0 : Real => And (0 < a0) (forall a : Real, abs a <= a0 ->
        Integrable (fun y : Real => Real.exp (a * y)) (nu : Measure Real)))))) := by
  obtain ⟨nu, m, sigma, hsigma, hmap, hmean, hv⟩ := d15a1b08_standardize mu hvar
  exact ⟨nu, m, sigma, hsigma.le, hmap, hmean, hv,
    d15a1b08_exp_transport mu nu m sigma hsigma hmap hexp⟩

open MeasureTheory ProbabilityTheory in
theorem solution
    (μ : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => 0 < a0 ∧ ∀ a : Real, abs a ≤ a0 →
      Integrable (fun x : Real => Real.exp (a * x)) (μ : Measure Real)) :
    ∃ (ν : ProbabilityMeasure Real) (m σ : Real),
      0 ≤ σ ∧
      Measure.map (fun y : Real => m + σ * y) (ν : Measure Real) = (μ : Measure Real) ∧
      MeasureTheory.integral (ν : Measure Real) (fun y : Real => y) = 0 ∧
      variance (fun y : Real => y) (ν : Measure Real) = 1 ∧
      (Exists fun a0 : Real => 0 < a0 ∧ ∀ a : Real, abs a ≤ a0 →
        Integrable (fun y : Real => Real.exp (a * y)) (ν : Measure Real)) := by
  rcases (variance_nonneg (fun x : Real => x) (μ : Measure Real)).lt_or_eq with hpos | hzero
  · exact d4d73198_pos_case μ hexp hpos
  · exact d4d73198_zero_case μ hexp hzero.symm
