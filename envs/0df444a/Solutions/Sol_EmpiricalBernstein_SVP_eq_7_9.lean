-- Prove2me | solution 1 for EmpiricalBernstein.SVP.eq_7_9
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T19:42:04.479392+00:00
-- url     : https://prove2.me/submissions/2bbff6ad-6c0c-4554-9dab-05393d2eff9a

import Mathlib
import Definitions.Def_EmpiricalBernstein_SVP_sampleVar

set_option autoImplicit false

open MeasureTheory ProbabilityTheory EmpiricalBernstein.SVP

lemma ebs79_ae {n : ℕ} (μs : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0) (i : Fin n) :
    ∀ᵐ z ∂(Measure.pi μs), z i ∈ Set.Icc (0 : ℝ) 1 := by
  have h : ∀ᵐ y ∂(μs i), y ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]; exact hμs i
  exact (Measure.quasiMeasurePreserving_eval μs i).ae h

lemma ebs79_intμ {n : ℕ} (μs : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0) (i : Fin n) (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable f (μs i) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hf.continuousOn
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  have h : ∀ᵐ y ∂(μs i), y ∈ Set.Icc (0 : ℝ) 1 := by
    rw [ae_iff]; exact hμs i
  filter_upwards [h] with x hx using hC x hx

lemma ebs79_eval {n : ℕ} (μs : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (i : Fin n) (f : ℝ → ℝ) (hf : Continuous f) :
    ∫ z, f (z i) ∂(Measure.pi μs) = ∫ y, f y ∂(μs i) := by
  conv_rhs => rw [← (measurePreserving_eval μs i).map_eq]
  rw [integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable]

lemma ebs79_integrable {n : ℕ} (μs : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0) (g : (Fin n → ℝ) → ℝ) (hg : Measurable g)
    (C : ℝ) (hb : ∀ z : Fin n → ℝ, (∀ i, z i ∈ Set.Icc (0 : ℝ) 1) → |g z| ≤ C) :
    Integrable g (Measure.pi μs) := by
  refine Integrable.of_bound hg.aestronglyMeasurable C ?_
  have h : ∀ᵐ z ∂(Measure.pi μs), ∀ i, z i ∈ Set.Icc (0 : ℝ) 1 :=
    ae_all_iff.2 (fun i => ebs79_ae μs hμs i)
  filter_upwards [h] with z hz
  simpa using hb z hz

lemma ebs79_pair {n : ℕ} (μs : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0) (i j : Fin n) (hij : i ≠ j) :
    ∫ z, (z i - z j) ^ 2 ∂(Measure.pi μs)
      = (∫ y, y ^ 2 ∂(μs i)) - 2 * (∫ y, y ∂(μs i)) * (∫ y, y ∂(μs j))
        + ∫ y, y ^ 2 ∂(μs j) := by
  have hi2 : Integrable (fun z : Fin n → ℝ => (z i) ^ 2) (Measure.pi μs) :=
    ebs79_integrable μs hμs _ (by fun_prop) 1 (fun z hz => by
      have := hz i
      rw [abs_of_nonneg (by positivity)]
      nlinarith [this.1, this.2])
  have hj2 : Integrable (fun z : Fin n → ℝ => (z j) ^ 2) (Measure.pi μs) :=
    ebs79_integrable μs hμs _ (by fun_prop) 1 (fun z hz => by
      have := hz j
      rw [abs_of_nonneg (by positivity)]
      nlinarith [this.1, this.2])
  have hij' : Integrable (fun z : Fin n → ℝ => z i * z j) (Measure.pi μs) :=
    ebs79_integrable μs hμs _ (by fun_prop) 1 (fun z hz => by
      have h1 := hz i
      have h2 := hz j
      rw [abs_of_nonneg (mul_nonneg h1.1 h2.1)]
      nlinarith [h1.1, h1.2, h2.1, h2.2])
  have hind : IndepFun (fun z : Fin n → ℝ => z i) (fun z : Fin n → ℝ => z j) (Measure.pi μs) :=
    (iIndepFun_pi (μ := μs) (X := fun _ (y : ℝ) => y) (fun _ => aemeasurable_id)).indepFun hij
  have hmul := hind.integral_mul_eq_mul_integral (measurable_pi_apply i).aestronglyMeasurable
    (measurable_pi_apply j).aestronglyMeasurable
  have e : (fun z : Fin n → ℝ => (z i - z j) ^ 2)
      = fun z => (z i) ^ 2 - 2 * (z i * z j) + (z j) ^ 2 := by
    funext z; ring
  have hA : Integrable (fun z : Fin n → ℝ => (z i) ^ 2 - 2 * (z i * z j)) (Measure.pi μs) :=
    hi2.sub (hij'.const_mul 2)
  have hB : Integrable (fun z : Fin n → ℝ => 2 * (z i * z j)) (Measure.pi μs) :=
    hij'.const_mul 2
  rw [e, integral_add hA hj2, integral_sub hi2 hB, integral_const_mul]
  have hmul' : ∫ z : Fin n → ℝ, z i * z j ∂(Measure.pi μs)
      = (∫ y, y ∂(μs i)) * ∫ y, y ∂(μs j) := by
    have h1 := ebs79_eval μs i (fun y => y) continuous_id
    have h2 := ebs79_eval μs j (fun y => y) continuous_id
    rw [← h1, ← h2]
    exact hmul
  rw [hmul', ebs79_eval μs i (fun y => y ^ 2) (by fun_prop),
    ebs79_eval μs j (fun y => y ^ 2) (by fun_prop)]
  ring

lemma ebs79_var {n : ℕ} (μs : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μs i)]
    (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0) (i : Fin n) :
    ∫ y, (y - ∫ w, w ∂(μs i)) ^ 2 ∂(μs i)
      = (∫ y, y ^ 2 ∂(μs i)) - (∫ y, y ∂(μs i)) ^ 2 := by
  set m := ∫ y, y ∂(μs i) with hm
  have h1 : Integrable (fun y : ℝ => y ^ 2) (μs i) := ebs79_intμ μs hμs i _ (by fun_prop)
  have h2 : Integrable (fun y : ℝ => 2 * m * y) (μs i) := ebs79_intμ μs hμs i _ (by fun_prop)
  have e : (fun y : ℝ => (y - m) ^ 2) = fun y => y ^ 2 - 2 * m * y + m ^ 2 := by
    funext y; ring
  have hA : Integrable (fun y : ℝ => y ^ 2 - 2 * m * y) (μs i) := h1.sub h2
  rw [e, integral_add hA (integrable_const _), integral_sub h1 h2, integral_const_mul]
  have hr : (μs i).real Set.univ = 1 := by simp
  simp only [integral_const, hr, smul_eq_mul, one_mul]
  rw [← hm]
  ring

theorem solution {n : ℕ} (hn : 2 ≤ n) (μs : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μs i)] (hμs : ∀ i, μs i (Set.Icc (0 : ℝ) 1)ᶜ = 0) :
    (1 / (n : ℝ)) * ∑ i, variance (fun y : ℝ => y) (μs i)
        ≤ ∫ z, sampleVar z ∂(Measure.pi μs) ∧
      (1 / (n : ℝ)) * ∑ i, ∫ y, (y - ∫ w, w ∂(μs i)) ^ 2 ∂(μs i)
          + 1 / (2 * (n : ℝ) * ((n : ℝ) - 1))
            * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i),
                ((∫ w, w ∂(μs i)) - ∫ w, w ∂(μs j)) ^ 2
        = ∫ z, sampleVar z ∂(Measure.pi μs) := by
  set m : Fin n → ℝ := fun i => ∫ y, y ∂(μs i) with hm
  set s : Fin n → ℝ := fun i => ∫ y, (y - ∫ w, w ∂(μs i)) ^ 2 ∂(μs i) with hs
  have hvar : ∀ i, variance (fun y : ℝ => y) (μs i) = s i := fun i => by
    rw [variance_eq_integral (X := fun y : ℝ => y) aemeasurable_id]
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hs0 : ∀ i, 0 ≤ s i := fun i => integral_nonneg (fun y => sq_nonneg _)
  -- the integral of sampleVar
  have hval : ∀ i j : Fin n, ∫ z, (z i - z j) ^ 2 / 2 ∂(Measure.pi μs)
      = (s i + s j + (m i - m j) ^ 2) / 2 - (if i = j then s i else 0) := by
    intro i j
    rw [integral_div]
    by_cases h : i = j
    · subst h
      simp
    · rw [ebs79_pair μs hμs i j h, if_neg h]
      have h1 := ebs79_var μs hμs i
      have h2 := ebs79_var μs hμs j
      simp only [hs, hm] at *
      rw [h1, h2]
      ring
  have hint : ∀ i j : Fin n, Integrable (fun z : Fin n → ℝ => (z i - z j) ^ 2 / 2)
      (Measure.pi μs) := fun i j =>
    ebs79_integrable μs hμs _ (by fun_prop) 1 (fun z hz => by
      have h1 := hz i
      have h2 := hz j
      rw [abs_of_nonneg (by positivity)]
      nlinarith [h1.1, h1.2, h2.1, h2.2])
  have hE : ∫ z, sampleVar z ∂(Measure.pi μs)
      = ((n : ℝ) * ((n : ℝ) - 1))⁻¹ * ∑ i, ∑ j, ((s i + s j + (m i - m j) ^ 2) / 2
          - (if i = j then s i else 0)) := by
    unfold sampleVar
    rw [integral_const_mul]
    congr 1
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hint i j))]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_finset_sum _ (fun j _ => hint i j)]
    exact Finset.sum_congr rfl (fun j _ => hval i j)
  have hsum : ∑ i : Fin n, ∑ j : Fin n, ((s i + s j + (m i - m j) ^ 2) / 2
          - (if i = j then s i else 0))
      = ((n : ℝ) - 1) * ∑ i, s i + (1 / 2) * ∑ i, ∑ j, (m i - m j) ^ 2 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    simp only [← Finset.mul_sum]
    generalize ∑ i, s i = A
    generalize ∑ i : Fin n, ∑ j : Fin n, (m i - m j) ^ 2 = D
    ring
  have key : ∀ i, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), (m i - m j) ^ 2
      = ∑ j, (m i - m j) ^ 2 := by
    intro i
    apply Finset.sum_filter_of_ne
    intro j _ hj h
    apply hj
    subst h
    simp
  have hD : 0 ≤ ∑ i : Fin n, ∑ j : Fin n, (m i - m j) ^ 2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
  have hfin : ((n : ℝ) * ((n : ℝ) - 1))⁻¹ * (((n : ℝ) - 1) * ∑ i, s i
        + (1 / 2) * ∑ i, ∑ j, (m i - m j) ^ 2)
      = (1 / (n : ℝ)) * ∑ i, s i + 1 / (2 * (n : ℝ) * ((n : ℝ) - 1))
          * ∑ i, ∑ j, (m i - m j) ^ 2 := by
    field_simp
  have hL : (1 / (n : ℝ)) * ∑ i, ∫ y, (y - ∫ w, w ∂(μs i)) ^ 2 ∂(μs i)
          + 1 / (2 * (n : ℝ) * ((n : ℝ) - 1))
            * ∑ i, ∑ j ∈ Finset.univ.filter (fun j => j ≠ i),
                ((∫ w, w ∂(μs i)) - ∫ w, w ∂(μs j)) ^ 2
      = (1 / (n : ℝ)) * ∑ i, s i + 1 / (2 * (n : ℝ) * ((n : ℝ) - 1))
          * ∑ i, ∑ j, (m i - m j) ^ 2 := by
    have := fun i => key i
    simp only [hs, hm] at this ⊢
    simp only [this]
  refine ⟨?_, ?_⟩
  · simp only [hvar]
    rw [hE, hsum, hfin]
    have : 0 ≤ 1 / (2 * (n : ℝ) * ((n : ℝ) - 1)) * ∑ i, ∑ j, (m i - m j) ^ 2 :=
      mul_nonneg (div_nonneg zero_le_one (mul_nonneg (by positivity) (by linarith))) hD
    linarith
  · rw [hE, hsum, hfin, hL]
