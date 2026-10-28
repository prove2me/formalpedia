-- Prove2me | solution 1 for ClosestString.PTAS.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T12:55:32.915521+00:00
-- url     : https://prove2.me/submissions/230ab45e-57b8-42ac-996d-6e899f87bc1c

import Mathlib

namespace ClosestString.PTAS.A3L4

open MeasureTheory ProbabilityTheory Real

lemma real_ineq {y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1) : (y ^ 2 - 1) / 2 ≤ y * Real.log y := by
  have h1 : 0 ≤ -Real.log y := by have := Real.log_nonpos hy0.le hy1; linarith
  have h2 := (Real.self_le_sinh_iff).2 h1
  rw [Real.sinh_neg, Real.sinh_log hy0] at h2
  have h3 : y * (-Real.log y) ≤ y * (-((y - y⁻¹) / 2)) := mul_le_mul_of_nonneg_left h2 hy0.le
  have h4 : y * y⁻¹ = 1 := mul_inv_cancel₀ hy0.ne'
  nlinarith

theorem main {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    {N : ℕ} (X : Fin N → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X Pr)
    (p : Fin N → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (hX_ber : ∀ i, Pr.real {ω | X i ω = 1} = p i ∧ Pr.real {ω | X i ω = 0} = 1 - p i)
    (δ : ℝ) (hδ : 0 < δ) :
    Pr.real {ω | (1 + δ) * (∫ ω', ∑ i, X i ω' ∂Pr) < ∑ i, X i ω} <
        (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (∫ ω', ∑ i, X i ω' ∂Pr) ∧
      Pr.real {ω | ∑ i, X i ω < (1 - δ) * (∫ ω', ∑ i, X i ω' ∂Pr)} ≤
        Real.exp (-(1 / 2) * (∫ ω', ∑ i, X i ω' ∂Pr) * δ ^ 2) := by
  have hA : ∀ i, MeasurableSet {ω | X i ω = 1} := fun i =>
    measurableSet_eq_fun (hX_meas i) measurable_const
  have hB : ∀ i, MeasurableSet {ω | X i ω = 0} := fun i =>
    measurableSet_eq_fun (hX_meas i) measurable_const
  have hae : ∀ i, ∀ᵐ ω ∂Pr, X i ω = 0 ∨ X i ω = 1 := by
    intro i
    have hdisj : Disjoint {ω | X i ω = 1} {ω | X i ω = 0} := by
      rw [Set.disjoint_left]
      intro ω h1 h0
      simp only [Set.mem_setOf_eq] at h1 h0
      rw [h1] at h0; norm_num at h0
    have hu : Pr.real ({ω | X i ω = 1} ∪ {ω | X i ω = 0}) = 1 := by
      rw [measureReal_union hdisj (hB i), (hX_ber i).1, (hX_ber i).2]; ring
    have hc : Pr.real ({ω | X i ω = 1} ∪ {ω | X i ω = 0})ᶜ = 0 := by
      rw [probReal_compl_eq_one_sub ((hA i).union (hB i)), hu]; ring
    rw [measureReal_eq_zero_iff] at hc
    rw [ae_iff]
    refine measure_mono_null ?_ hc
    intro ω hω
    simp only [Set.mem_setOf_eq, not_or] at hω
    simp [hω.1, hω.2]
  have hkey : ∀ i (g : ℝ → ℝ), (fun ω => g (X i ω)) =ᵐ[Pr]
      fun ω => g 0 + (g 1 - g 0) * ({ω | X i ω = 1}.indicator (1 : Ω → ℝ) ω) := by
    intro i g
    filter_upwards [hae i] with ω h
    rcases h with h | h <;> simp [Set.indicator, h]
  have hint_g : ∀ i (g : ℝ → ℝ), Integrable (fun ω => g (X i ω)) Pr ∧
      ∫ ω, g (X i ω) ∂Pr = g 0 + (g 1 - g 0) * p i := by
    intro i g
    have hi2 : Integrable (fun ω => (g 1 - g 0) * ({ω | X i ω = 1}.indicator (1 : Ω → ℝ) ω)) Pr :=
      ((integrable_const (1:ℝ)).indicator (hA i)).const_mul _
    have hi : Integrable
        (fun ω => g 0 + (g 1 - g 0) * ({ω | X i ω = 1}.indicator (1 : Ω → ℝ) ω)) Pr :=
      (integrable_const _).add hi2
    refine ⟨hi.congr (hkey i g).symm, ?_⟩
    rw [integral_congr_ae (hkey i g), integral_add (integrable_const _) hi2, integral_const_mul,
      integral_indicator_one (hA i), (hX_ber i).1]
    simp
  have hmu : ∫ ω', ∑ i, X i ω' ∂Pr = ∑ i, p i := by
    have hXi : ∀ i, Integrable (fun ω => X i ω) Pr := fun i => (hint_g i id).1
    rw [integral_finsetSum _ (fun i _ => hXi i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have := (hint_g i id).2
    simpa using this
  have hmgf : ∀ i t, mgf (X i) Pr t = 1 + (exp t - 1) * p i := by
    intro i t
    have := (hint_g i (fun x => exp (t * x))).2
    simp only [mul_zero, exp_zero, mul_one] at this
    unfold mgf
    exact this
  have hexpint : ∀ i t, Integrable (fun ω => exp (t * X i ω)) Pr := fun i t =>
    (hint_g i (fun x => exp (t * x))).1
  have hmgfsum : ∀ t, mgf (∑ i, X i) Pr t = ∏ i, (1 + (exp t - 1) * p i) := by
    intro t; rw [hX_indep.mgf_sum hX_meas]; simp [hmgf]
  have hintsum : ∀ t, Integrable (fun ω => exp (t * (∑ i, X i) ω)) Pr := fun t =>
    hX_indep.integrable_exp_mul_sum hX_meas (fun i _ => hexpint i t)
  rw [hmu]
  set μ := ∑ i, p i with hμ
  have hμ0 : 0 ≤ μ := Finset.sum_nonneg (fun i _ => (hp i).1.le)
  have hexpμ : ∀ c, ∏ i, exp (c * p i) = exp (c * μ) := by
    intro c; rw [← Real.exp_sum, hμ, Finset.mul_sum]
  constructor
  · rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp [hμ]
    · have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
      have hd1 : 0 < 1 + δ := by linarith
      set t := Real.log (1 + δ) with ht
      have ht0 : 0 ≤ t := Real.log_nonneg (by linarith)
      have het : exp t = 1 + δ := Real.exp_log hd1
      have h1 := measure_ge_le_exp_mul_mgf (X := ∑ i, X i) (μ := Pr) ((1 + δ) * μ) ht0
        (hintsum t)
      rw [hmgfsum, het] at h1
      have hprod : ∏ i, (1 + (1 + δ - 1) * p i) < ∏ i, exp (δ * p i) := by
        apply Finset.prod_lt_prod_of_nonempty
        · intro i _; nlinarith [(hp i).1]
        · intro i _
          have := Real.add_one_lt_exp (x := δ * p i) (mul_pos hδ (hp i).1).ne'
          linarith
        · exact hne
      rw [hexpμ] at hprod
      have hsub : {ω | (1 + δ) * μ < ∑ i, X i ω} ⊆ {ω | (1 + δ) * μ ≤ (∑ i, X i) ω} := by
        intro ω hω
        simp only [Set.mem_setOf_eq, Finset.sum_apply] at hω ⊢
        exact hω.le
      have hrhs : (exp δ / (1 + δ) ^ (1 + δ)) ^ μ = exp (-t * ((1 + δ) * μ)) * exp (δ * μ) := by
        rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
        congr 1
        rw [Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp, Real.log_rpow hd1]
        ring
      calc Pr.real {ω | (1 + δ) * μ < ∑ i, X i ω}
          ≤ Pr.real {ω | (1 + δ) * μ ≤ (∑ i, X i) ω} := measureReal_mono hsub
        _ ≤ _ := h1
        _ < exp (-t * ((1 + δ) * μ)) * exp (δ * μ) := mul_lt_mul_of_pos_left hprod (exp_pos _)
        _ = _ := hrhs.symm
  · rcases lt_or_ge δ 1 with hδ1 | hδ1
    · have hd1 : 0 < 1 - δ := by linarith
      set t := Real.log (1 - δ) with ht
      have ht0 : t ≤ 0 := Real.log_nonpos hd1.le (by linarith)
      have het : exp t = 1 - δ := Real.exp_log hd1
      have h1 := measure_le_le_exp_mul_mgf (X := ∑ i, X i) (μ := Pr) ((1 - δ) * μ) ht0
        (hintsum t)
      rw [hmgfsum, het] at h1
      have hprod : ∏ i, (1 + (1 - δ - 1) * p i) ≤ ∏ i, exp (-δ * p i) := by
        apply Finset.prod_le_prod
        · intro i _; nlinarith [(hp i).1, (hp i).2]
        · intro i _
          have := Real.add_one_le_exp (-δ * p i)
          linarith
      rw [hexpμ] at hprod
      have hsub : {ω | ∑ i, X i ω < (1 - δ) * μ} ⊆ {ω | (∑ i, X i) ω ≤ (1 - δ) * μ} := by
        intro ω hω
        simp only [Set.mem_setOf_eq, Finset.sum_apply] at hω ⊢
        exact hω.le
      have hreal := real_ineq hd1 (by linarith : 1 - δ ≤ 1)
      calc Pr.real {ω | ∑ i, X i ω < (1 - δ) * μ}
          ≤ Pr.real {ω | (∑ i, X i) ω ≤ (1 - δ) * μ} := measureReal_mono hsub
        _ ≤ _ := h1
        _ ≤ exp (-t * ((1 - δ) * μ)) * exp (-δ * μ) :=
          mul_le_mul_of_nonneg_left hprod (exp_pos _).le
        _ ≤ _ := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          nlinarith [mul_le_mul_of_nonneg_left hreal hμ0]
    · have hae0 : ∀ᵐ ω ∂Pr, 0 ≤ ∑ i, X i ω := by
        have : ∀ᵐ ω ∂Pr, ∀ i, X i ω = 0 ∨ X i ω = 1 := ae_all_iff.2 hae
        filter_upwards [this] with ω h
        exact Finset.sum_nonneg (fun i _ => by rcases h i with h | h <;> simp [h])
      have hnull : Pr {ω | ∑ i, X i ω < (1 - δ) * μ} = 0 := by
        refine measure_mono_null ?_ (ae_iff.1 hae0)
        intro ω hω
        simp only [Set.mem_setOf_eq, not_le] at hω ⊢
        have : (1 - δ) * μ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hμ0
        linarith
      rw [measureReal_def, hnull, ENNReal.toReal_zero]
      exact (exp_pos _).le

end ClosestString.PTAS.A3L4

open MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (Pr : Measure Ω) [IsProbabilityMeasure Pr]
    {N : ℕ} (X : Fin N → Ω → ℝ) (hX_meas : ∀ i, Measurable (X i)) (hX_indep : iIndepFun X Pr)
    (p : Fin N → ℝ) (hp : ∀ i, 0 < p i ∧ p i < 1)
    (hX_ber : ∀ i, Pr.real {ω | X i ω = 1} = p i ∧ Pr.real {ω | X i ω = 0} = 1 - p i)
    (δ : ℝ) (hδ : 0 < δ) :
    Pr.real {ω | (1 + δ) * (∫ ω', ∑ i, X i ω' ∂Pr) < ∑ i, X i ω} <
        (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (∫ ω', ∑ i, X i ω' ∂Pr) ∧
      Pr.real {ω | ∑ i, X i ω < (1 - δ) * (∫ ω', ∑ i, X i ω' ∂Pr)} ≤
        Real.exp (-(1 / 2) * (∫ ω', ∑ i, X i ω' ∂Pr) * δ ^ 2) :=
  ClosestString.PTAS.A3L4.main Pr X hX_meas hX_indep p hp hX_ber δ hδ

#print axioms solution
