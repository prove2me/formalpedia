-- Prove2me | solution 1 for FunctionalInequalities.Probability.pi_normalizedSum_moments_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:58:26.2475+00:00
-- url     : https://prove2.me/submissions/00d432c5-a832-4fb2-8f40-d6e682227b88

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory ProbabilityTheory Filter
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section MeasurableSpace
variable {E : Type*}
variable [MeasurableSpace E]
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
/-- **Normalized sums of independent copies.** If `f ∈ L²(μ)` has mean `0` and second moment `1`,
then `(Σ_i f(x_i))/√N` has mean `0` and second moment `1` under `μ^N` (`N > 0`). -/
theorem solution
    (μ : Measure E) [IsProbabilityMeasure μ] (f : E → ℝ) (hf2 : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hf1 : ∫ x, f x ^ 2 ∂μ = 1)
    (N : ℕ) (hN : 0 < N) :
    MemLp (fun x : Fin N → E => (∑ i, f (x i)) / Real.sqrt N) 2
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → E, (∑ i, f (x i)) / Real.sqrt N
        ∂(Measure.pi (fun _ : Fin N => μ))) = 0 ∧
      (∫ x : Fin N → E, ((∑ i, f (x i)) / Real.sqrt N) ^ 2
        ∂(Measure.pi (fun _ : Fin N => μ))) = 1 := by
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  let S : (Fin N → E) → ℝ := fun x => ∑ i, f (x i)
  have hEval2 (i : Fin N) : MemLp (fun x : Fin N → E => f (x i)) 2 ν := by
    exact hf2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) i)
  have hS2 : MemLp S 2 ν := by
    exact memLp_finsetSum Finset.univ (fun i _ => hEval2 i)
  have hEval0 (i : Fin N) : (∫ x : Fin N → E, f (x i) ∂ν) = 0 := by
    have he := measurePreserving_eval (fun _ : Fin N => μ) i
    have hm : AEStronglyMeasurable f (ν.map (Function.eval i)) := by
      rw [he.map_eq]
      exact hf2.aestronglyMeasurable
    calc
      (∫ x : Fin N → E, f (x i) ∂ν) =
          ∫ x, f x ∂(ν.map (Function.eval i)) := (integral_map he.measurable.aemeasurable hm).symm
      _ = 0 := by rw [he.map_eq]; exact hf0
  have hS0 : (∫ x, S x ∂ν) = 0 := by
    calc
      (∫ x, S x ∂ν) = ∑ i : Fin N, ∫ x, f (x i) ∂ν :=
        integral_finsetSum _ (fun i _ => (hEval2 i).integrable one_le_two)
      _ = 0 := by simp_rw [hEval0]; simp
  have hVarf : variance f μ = 1 := by
    rw [variance_eq_sub hf2]
    simp only [Pi.pow_apply]
    rw [hf1, hf0]
    norm_num
  have hVarS : variance S ν = (N : ℝ) := by
    have h := variance_sum_pi (μ := fun _ : Fin N => μ) (X := fun _ => f) (fun _ => hf2)
    have heq : (∑ i : Fin N, fun x : Fin N → E => f (x i)) = S := by
      funext x
      simp [S]
    rw [heq] at h
    simpa [ν, hVarf] using h
  have hSsq : (∫ x, S x ^ 2 ∂ν) = (N : ℝ) := by
    rw [variance_eq_sub hS2, hS0] at hVarS
    simpa using hVarS
  have hNormalized2 : MemLp (fun x : Fin N → E => S x / Real.sqrt N) 2 ν := by
    simpa [div_eq_mul_inv] using hS2.mul_const (Real.sqrt N)⁻¹
  refine ⟨hNormalized2, ?_, ?_⟩
  · change (∫ x, S x / Real.sqrt N ∂ν) = 0
    rw [integral_div, hS0]
    simp
  · change (∫ x, (S x / Real.sqrt N) ^ 2 ∂ν) = 1
    simp_rw [div_pow]
    rw [integral_div, hSsq, Real.sq_sqrt (Nat.cast_nonneg N)]
    exact div_self (by exact_mod_cast hN.ne')
