-- Prove2me | solution 1 for BanditAlgorithm.subgaussian_sample_mean_confidence_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-07-18T14:26:02.515024+00:00
-- url     : https://prove2.me/submissions/b8865f63-bc59-4ac6-a548-d4b463d6b014

import Theorems.Thm_BanditAlgorithm_subgaussian_sample_mean_tail_bound

open MeasureTheory ProbabilityTheory Real NNReal

theorem solution
    {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) {X : Fin n → Ω → ℝ} {m : ℝ} {σ : ℝ≥0} (hσ : 0 < σ)
    (h_indep : iIndepFun (fun i ω ↦ X i ω - m) P)
    (h_subG : ∀ i, HasSubgaussianMGF (fun ω ↦ X i ω - m) (σ ^ 2) P)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    P.real {ω | (∑ i, X i ω) / n + Real.sqrt (2 * (σ : ℝ) ^ 2 * log (1 / δ) / n) ≤ m} ≤ δ := by
  let ε : ℝ := Real.sqrt (2 * (σ : ℝ) ^ 2 * log (1 / δ) / n)
  have hε : 0 ≤ ε := Real.sqrt_nonneg _
  have htail :=
    (BanditAlgorithm.subgaussian_sample_mean_tail_bound hn hσ h_indep h_subG hε).2
  have hset :
      {ω | (∑ i, X i ω) / n + ε ≤ m} =
        {ω | (∑ i, X i ω) / n ≤ m - ε} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [show Real.sqrt (2 * (σ : ℝ) ^ 2 * log (1 / δ) / n) = ε from rfl, hset]
  calc
    P.real {ω | (∑ i, X i ω) / n ≤ m - ε} ≤
        exp (-((n : ℝ) * ε ^ 2) / (2 * (σ : ℝ) ^ 2)) := htail
    _ = δ := by
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      have hσR : (0 : ℝ) < σ := by exact_mod_cast hσ
      have hδ0 : 0 < δ := hδ.1
      have hδ1 : δ < 1 := hδ.2
      have hdiv : 1 < 1 / δ := by
        rw [one_div]
        exact (one_lt_inv₀ hδ0).2 hδ1
      have hlog : 0 < log (1 / δ) := Real.log_pos hdiv
      have hrad : 0 ≤ 2 * (σ : ℝ) ^ 2 * log (1 / δ) / n := by positivity
      have hεsq : ε ^ 2 = 2 * (σ : ℝ) ^ 2 * log (1 / δ) / n := by
        simpa [ε] using Real.sq_sqrt hrad
      rw [hεsq]
      have hexp :
          -((n : ℝ) * (2 * (σ : ℝ) ^ 2 * log (1 / δ) / n)) /
              (2 * (σ : ℝ) ^ 2) = log δ := by
        rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt hδ0), Real.log_one]
        field_simp [ne_of_gt hnR, ne_of_gt hσR, ne_of_gt hδ0]
        ring
      rw [hexp, Real.exp_log hδ0]
