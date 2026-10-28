-- Prove2me | solution 1 for FunctionalInequalities.Probability.tendsto_variance_quadratic_matrix_forms_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:40:46.530998+00:00
-- url     : https://prove2.me/submissions/bd6ef074-f2f0-4cb4-900f-1f8f6084749e

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_QuadraticVariance
import Theorems.Thm_FunctionalInequalities_Probability_tendsto_variance_finite_linear_combination_readable

noncomputable section
open MeasureTheory Filter Matrix
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 500000 in
theorem solution {n : ℕ}
    (mu : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (h4 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 4 (mu : Measure _))
    {seq : ℕ → Matrix (Fin n) (Fin n) ℝ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hseq : Tendsto seq atTop (𝓝 A)) :
    Tendsto (fun k => ProbabilityTheory.variance
      (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, seq k i j * x i * x j) (mu : Measure _))
      atTop (𝓝 (ProbabilityTheory.variance
        (fun x : EuclideanSpace ℝ (Fin n) => ∑ i, ∑ j, A i j * x i * x j) (mu : Measure _))) := by
  classical
  have ht : ENNReal.HolderTriple (4 : ENNReal) 4 2 := by
    constructor
    rw [← ENNReal.coe_ofNat 4, ← ENNReal.coe_ofNat 2,
      ← ENNReal.coe_inv (by norm_num : (4 : NNReal) ≠ 0),
      ← ENNReal.coe_inv (by norm_num : (2 : NNReal) ≠ 0),
      ← ENNReal.coe_add]
    norm_num
  have hcoord (i : Fin n) : MemLp (fun x : EuclideanSpace ℝ (Fin n) => x i) 4 (mu : Measure _) := by
    simpa only [id_eq, EuclideanSpace.inner_basisFun_real] using
      h4.inner_const (𝕜 := ℝ) (EuclideanSpace.basisFun (Fin n) ℝ i)
  have hprod (p : Fin n × Fin n) : MemLp
      (fun x : EuclideanSpace ℝ (Fin n) => x p.1 * x p.2) 2 (mu : Measure _) :=
    (hcoord p.2).mul (hcoord p.1) (hpqr := ht)
  have hc (p : Fin n × Fin n) : Tendsto (fun k => seq k p.1 p.2) atTop (𝓝 (A p.1 p.2)) := by
    have hcont : Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M p.1 p.2) := by fun_prop
    exact hcont.continuousAt.tendsto.comp hseq
  have h := FunctionalInequalities.Probability.tendsto_variance_finite_linear_combination_readable mu
    (fun p : Fin n × Fin n => fun x : EuclideanSpace ℝ (Fin n) => x p.1 * x p.2) hprod
    (fun k p => seq k p.1 p.2) (fun p => A p.1 p.2) hc
  simpa only [Fintype.sum_prod_type, mul_assoc] using h
