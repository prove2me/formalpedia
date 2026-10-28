-- Prove2me | solution 1 for FunctionalInequalities.KLS.BKL.exists_norm_cumulant_le_isotropic_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:29:41.243332+00:00
-- url     : https://prove2.me/submissions/feaa1289-7eb3-4b0d-a605-a22825e4b7e2

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Isotropic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Cumulant_Local
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Bound
import Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_norm_cumulant_le_of_moment_bounds_readable
import Theorems.Thm_FunctionalInequalities_KLS_Isotropic_integral_norm_sq_readable

section
noncomputable section
open MeasureTheory Filter Topology InnerProductSpace
section
open FunctionalInequalities.Energy FunctionalInequalities.Energy.Euclidean FunctionalInequalities.Probability
section Euclidean
variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁] [CompleteSpace V₁]
  [MeasurableSpace V₁] [BorelSpace V₁] [SecondCountableTopology V₁] [FiniteDimensional ℝ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [CompleteSpace V₂]
  [MeasurableSpace V₂] [BorelSpace V₂] [SecondCountableTopology V₂] [FiniteDimensional ℝ V₂]
section
open scoped RealInnerProductSpace in
/-- **All moments of isotropic log-concave laws on `ℝⁿ`** are bounded by constants depending only on
`n` and the order, with radius `R = 2√(n+1)` (quantitative Borell; BKL Section 2, p. 5). -/
theorem FunctionalInequalities.KLS.LogConcave.integral_norm_pow_le_of_isotropic {n : ℕ}
    {ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))} (hlc : KLS.LogConcave ν)
    (hiso : KLS.Isotropic ν) (p : ℕ) :
    let R : ℝ := 2 * Real.sqrt ((n : ℝ) + 1)
    Integrable (fun v : EuclideanSpace ℝ (Fin n) => ‖v‖ ^ p) (ν : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∫ v, ‖v‖ ^ p ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) ≤
        (p.factorial : ℝ) / (Real.log 3 / (4 * R)) ^ p *
          ((3 : ℝ) ^ (3 / 4 : ℝ) / (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ)))) := by
  have hLC : KLS.BorelLogConcave ν := (KLS.LogConcave.borel_iff ν).1 hlc
  have hint : Integrable (fun v : EuclideanSpace ℝ (Fin n) => ‖v‖ ^ 2) (ν : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [id_eq] using (memLp_two_iff_integrable_sq_norm hiso.memLp_two.1).1 hiso.memLp_two
  exact hLC.integral_norm_pow_le_of_second_bound hint hiso.integral_norm_sq_readable.le p
end
end Euclidean
end
end
end

section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ContDiff
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
section CompactSupport
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
/-- A law with compact support has every exponential moment. -/
theorem FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_exp (μ : Measure F) [IsFiniteMeasure μ]
    (hc : IsCompact μ.support) (r : ℝ) : Integrable (fun x => Real.exp (r * ‖x‖)) μ := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : F)
  refine (integrable_const (Real.exp (|r| * max R 0))).mono' (by fun_prop) ?_
  filter_upwards [μ.support_mem_ae] with x hx
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  calc
    r * ‖x‖ ≤ |r| * ‖x‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |r| * max R 0 := by
      gcongr
      exact (by simpa using hR hx : ‖x‖ ≤ R).trans (le_max_left _ _)
end CompactSupport
end
end

noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace ContDiff
open FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis.BakryEmery
variable {n : ℕ}
/-- A-priori cumulant bound in a fixed dimension. -/
theorem solution (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      FunctionalInequalities.KLS.LogConcave ν → FunctionalInequalities.KLS.Isotropic ν → IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support →
        ‖FunctionalInequalities.Analysis.BakryEmery.cumulant (ν : Measure (EuclideanSpace ℝ (Fin n))) m‖ ≤ C := by
  classical
  let R : ℝ := 2 * Real.sqrt ((n : ℝ) + 1)
  let M : ℕ → ℝ := fun i =>
    (i.factorial : ℝ) / (Real.log 3 / (4 * R)) ^ i *
      ((3 : ℝ) ^ (3 / 4 : ℝ) / (1 - (3 : ℝ) ^ (-(1 / 4 : ℝ))))
  let D : ℝ := 1 + ∑ i ∈ Finset.range (m + 1), |M i|
  have hsum : 0 ≤ ∑ i ∈ Finset.range (m + 1), |M i| :=
    Finset.sum_nonneg (fun i _ => abs_nonneg (M i))
  have hD : 1 ≤ D := by dsimp [D]; linarith
  refine ⟨(m.factorial : ℝ) ^ 2 * D ^ m,
    mul_nonneg (sq_nonneg _) (pow_nonneg (by linarith) _), ?_⟩
  intro ν hlc hiso hc
  apply FunctionalInequalities.Analysis.BakryEmery.norm_cumulant_le_of_moment_bounds_readable (ν : Measure (EuclideanSpace ℝ (Fin n)))
    (r := 1) zero_lt_one (FunctionalInequalities.Analysis.BakryEmery.compact_support_integrable_exp _ hc 1)
  intro i hi him
  have hmoment : (∫ x, ‖x‖ ^ i ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) ≤ M i :=
    (FunctionalInequalities.KLS.LogConcave.integral_norm_pow_le_of_isotropic hlc hiso i).2
  have hterm : |M i| ≤ ∑ j ∈ Finset.range (m + 1), |M j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (M j))
      (Finset.mem_range.mpr (by omega))
  calc
    (∫ x, ‖x‖ ^ i ∂(ν : Measure (EuclideanSpace ℝ (Fin n)))) ≤ M i := hmoment
    _ ≤ |M i| := le_abs_self _
    _ ≤ D := by dsimp [D]; linarith
    _ = D ^ 1 := (pow_one D).symm
    _ ≤ D ^ i := pow_le_pow_right₀ hD hi
