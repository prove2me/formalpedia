-- Prove2me | solution 1 for FunctionalInequalities.Analysis.bounded_trace_quadratic_weak_derivative_data_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:37:59.447473+00:00
-- url     : https://prove2.me/submissions/26c03f10-69af-456b-97ae-7cddebd56008

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakDerivative
import Theorems.Thm_FunctionalInequalities_Analysis_hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two_readable
import Theorems.Thm_FunctionalInequalities_Analysis_trace_mul_mul_mul_eq_sum_readable

noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ContDiff Topology BigOperators
section BoundedTraceQuadratic
open scoped ContDiff Topology
/-- For a globally bounded measurable matrix field `A` with compact-local L2 weak entry derivatives `DA`, the
trace quadratic `tr(B A B A)` is globally bounded, locally integrable, and has the weak coordinate derivatives
`2 tr(B A B DAₖ)`, which are L2 on every compact set. All finite dimensions are allowed. -/
theorem solution {d n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ)
    (DA : Fin d → EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ)
    {M : NNReal}
    (hmeas : ∀ i j, Measurable (fun x => A x i j))
    (hbound : ∀ x i j, ‖A x i j‖ ≤ (M : ℝ))
    (hweak : ∀ k i j, FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => A x i j) (fun x => DA k x i j)
      (EuclideanSpace.basisFun (Fin d) ℝ k))
    (hDA2 : ∀ k i j, ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
      MemLp (fun x => DA k x i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S)) :
    ∃ C : ℝ, 0 ≤ C ∧ (∀ x, ‖(B * A x * B * A x).trace‖ ≤ C) ∧
      LocallyIntegrable (fun x => (B * A x * B * A x).trace)
        (volume : Measure (EuclideanSpace ℝ (Fin d))) ∧
      ∀ k : Fin d,
        FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => (B * A x * B * A x).trace)
          (fun x => 2 * (B * A x * B * DA k x).trace)
          (EuclideanSpace.basisFun (Fin d) ℝ k) ∧
        ∀ S : Set (EuclideanSpace ℝ (Fin d)), IsCompact S →
          MemLp (fun x => 2 * (B * A x * B * DA k x).trace) 2
            ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict S) := by
  classical
  let C : ℝ := ∑ q : Fin n × Fin n × Fin n × Fin n,
    ‖B q.1 q.2.1 * B q.2.2.1 q.2.2.2‖ * (M : ℝ) ^ 2
  have hb (x : EuclideanSpace ℝ (Fin d)) : ‖(B * A x * B * A x).trace‖ ≤ C := by
    rw [FunctionalInequalities.Analysis.trace_mul_mul_mul_eq_sum_readable]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro q _
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    rw [norm_mul]
    have h1 := hbound x q.2.1 q.2.2.1
    have h2 := hbound x q.2.2.2 q.1
    simpa only [pow_two] using mul_le_mul h1 h2
      (norm_nonneg (A x q.2.2.2 q.1)) (NNReal.coe_nonneg M)
  have hmeasf : Measurable (fun x => (B * A x * B * A x).trace) := by
    simp_rw [FunctionalInequalities.Analysis.trace_mul_mul_mul_eq_sum_readable]
    fun_prop
  have htop : MemLp (fun x => (B * A x * B * A x).trace) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    memLp_top_of_bound hmeasf.aestronglyMeasurable C (Filter.Eventually.of_forall hb)
  have htopA (i j : Fin n) : MemLp (fun x => A x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
    memLp_top_of_bound (hmeas i j).aestronglyMeasurable (M : ℝ)
      (Filter.Eventually.of_forall fun x => hbound x i j)
  refine ⟨C, Finset.sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (sq_nonneg _)),
    hb, htop.locallyIntegrable le_top, ?_⟩
  intro k
  exact FunctionalInequalities.Analysis.hasWeakDerivAlong_trace_quadratic_of_locally_memLp_two_readable B
    (fun i j => hweak k i j) htopA (fun i j => hDA2 k i j)
