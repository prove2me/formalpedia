-- Prove2me | solution 1 for FunctionalInequalities.Probability.sum_variance_entries_eq_integral_trace_sub_trace_mean_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:39:25.401554+00:00
-- url     : https://prove2.me/submissions/ae7523d6-dbc6-49d5-a75d-1c9d7dc98910

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Moments
import Theorems.Thm_FunctionalInequalities_Analysis_sum_matrix_product_entry_mul_eq_trace_readable

open MeasureTheory
section FiniteVarianceSum
section
private theorem FunctionalInequalities.Probability.sum_variance_eq_integral_sum_sq_sub_sum_integral_sq {alpha I : Type*}
    [MeasurableSpace alpha] [Fintype I] (mu : Measure alpha) [IsProbabilityMeasure mu]
    (F : I → alpha → ℝ) (hF : ∀ i, MemLp (F i) 2 mu) :
    (∑ i, ProbabilityTheory.variance (F i) mu) =
      (∫ x, ∑ i, F i x ^ 2 ∂mu) - ∑ i, (∫ x, F i x ∂mu) ^ 2 := by
  classical
  calc
    _ = ∑ i, ((∫ x, F i x ^ 2 ∂mu) - (∫ x, F i x ∂mu) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      exact ProbabilityTheory.variance_eq_sub (hF i)
    _ = (∑ i, ∫ x, F i x ^ 2 ∂mu) - ∑ i, (∫ x, F i x ∂mu) ^ 2 := by
      rw [Finset.sum_sub_distrib]
    _ = _ := by rw [integral_finsetSum _ (fun i _ => (hF i).integrable_sq)]
end
end FiniteVarianceSum
section MatrixVarianceTrace
open MeasureTheory Matrix
/-- For an almost-everywhere symmetric random matrix `H` with L2 entries and symmetric mean `M` under a probability
measure, the entry variances sum to `∫ tr(H H) - tr(M M)`; all finite dimensions. -/
theorem solution {alpha : Type*} [MeasurableSpace alpha]
    {n : ℕ} (mu : Measure alpha) [IsProbabilityMeasure mu]
    (H : alpha → Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) (hH : ∀ᵐ x ∂mu, (H x).IsSymm)
    (hH2 : ∀ i j, MemLp (fun x => H x i j) 2 mu)
    (hmean : ∀ i j, (∫ x, H x i j ∂mu) = M i j) :
    (∑ p : Fin n × Fin n, ProbabilityTheory.variance (fun x => H x p.1 p.2) mu) =
      (∫ x, (H x * H x).trace ∂mu) - (M * M).trace := by
  classical
  have hI : (1 : Matrix (Fin n) (Fin n) ℝ).IsSymm := by
    change (1 : Matrix (Fin n) (Fin n) ℝ).transpose = 1
    simp only [Matrix.transpose_one]
  have htrace : (fun x => ∑ p : Fin n × Fin n, H x p.1 p.2 ^ 2) =ᵐ[mu]
      (fun x => (H x * H x).trace) := by
    filter_upwards [hH] with x hx
    simpa only [Matrix.one_mul, Matrix.mul_one, pow_two] using
      FunctionalInequalities.Analysis.sum_matrix_product_entry_mul_eq_trace_readable (1 : Matrix (Fin n) (Fin n) ℝ) (H x) (H x) hI hx
  have hMtrace : (∑ p : Fin n × Fin n, M p.1 p.2 ^ 2) = (M * M).trace := by
    simpa only [Matrix.one_mul, Matrix.mul_one, pow_two] using
      FunctionalInequalities.Analysis.sum_matrix_product_entry_mul_eq_trace_readable (1 : Matrix (Fin n) (Fin n) ℝ) M M hI hM
  rw [FunctionalInequalities.Probability.sum_variance_eq_integral_sum_sq_sub_sum_integral_sq mu
    (fun p : Fin n × Fin n => fun x => H x p.1 p.2) (fun p => hH2 p.1 p.2)]
  rw [integral_congr_ae htrace]
  simp_rw [hmean]
  rw [hMtrace]
