-- Prove2me | solution 1 for BanditAlgorithm.subgaussian_sample_mean_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-18T03:39:53.83928+00:00
-- url     : https://prove2.me/submissions/b028eaa8-2939-47ae-adef-ed3c646b4c5b

import Mathlib.Probability.Moments.SubGaussian

open MeasureTheory ProbabilityTheory Real NNReal

theorem solution
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {m : ℝ} {σ : ℝ≥0} (hσ : 0 < σ)
    (h_indep : iIndepFun (fun i ω ↦ X i ω - m) P)
    (h_subG : ∀ i, HasSubgaussianMGF (fun ω ↦ X i ω - m) (σ ^ 2) P)
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | m + ε ≤ (∑ i, X i ω) / n} ≤
        exp (-((n : ℝ) * ε ^ 2) / (2 * (σ : ℝ) ^ 2)) ∧
    P.real {ω | (∑ i, X i ω) / n ≤ m - ε} ≤
        exp (-((n : ℝ) * ε ^ 2) / (2 * (σ : ℝ) ^ 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
  have hscale : 0 ≤ (n : ℝ) * ε := mul_nonneg (by positivity) hε
  constructor
  · have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (X := fun i ω ↦ X i ω - m) h_indep
      (c := fun _ : Fin n ↦ σ ^ 2) (s := Finset.univ)
      (fun i _ ↦ h_subG i) hscale
    have hset : {ω | m + ε ≤ (∑ i, X i ω) / n} =
        {ω | (n : ℝ) * ε ≤ ∑ i, (X i ω - m)} := by
      ext ω
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Set.mem_setOf_eq]
      rw [le_div_iff₀ hnR]
      constructor <;> intro hω <;> nlinarith
    rw [hset]
    calc
      P.real {ω | (n : ℝ) * ε ≤ ∑ i, (X i ω - m)}
          ≤ exp (-((n : ℝ) * ε) ^ 2 /
              (2 * ((∑ _ : Fin n, σ ^ 2 : ℝ≥0) : ℝ))) := h
      _ = exp (-((n : ℝ) * ε ^ 2) / (2 * (σ : ℝ) ^ 2)) := by
        congr 1
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow]
        field_simp [ne_of_gt hnR, ne_of_gt hσR]
  · have h_indep_neg : iIndepFun (fun i ω ↦ -(X i ω - m)) P := by
      simpa [Function.comp_def] using
        h_indep.comp (fun _ ↦ fun x : ℝ ↦ -x) (fun _ ↦ measurable_neg)
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (X := fun i ω ↦ -(X i ω - m)) h_indep_neg
      (c := fun _ : Fin n ↦ σ ^ 2) (s := Finset.univ)
      (fun i _ ↦ (h_subG i).neg) hscale
    have hset : {ω | (∑ i, X i ω) / n ≤ m - ε} =
        {ω | (n : ℝ) * ε ≤ ∑ i, -(X i ω - m)} := by
      ext ω
      simp only [Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Set.mem_setOf_eq]
      rw [div_le_iff₀ hnR]
      constructor <;> intro hω <;> nlinarith
    rw [hset]
    calc
      P.real {ω | (n : ℝ) * ε ≤ ∑ i, -(X i ω - m)}
          ≤ exp (-((n : ℝ) * ε) ^ 2 /
              (2 * ((∑ _ : Fin n, σ ^ 2 : ℝ≥0) : ℝ))) := h
      _ = exp (-((n : ℝ) * ε ^ 2) / (2 * (σ : ℝ) ^ 2)) := by
        congr 1
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow]
        field_simp [ne_of_gt hnR, ne_of_gt hσR]
