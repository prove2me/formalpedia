-- Prove2me | solution 1 for FunctionalInequalities.Probability.integral_normalizedSum_mul_comp_eval_pi_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:20:42.510655+00:00
-- url     : https://prove2.me/submissions/87b15172-7286-4b36-8f10-cc202bec1f88

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Product
import Theorems.Thm_FunctionalInequalities_Probability_integral_mul_comp_eval_pi_readable

noncomputable section
open MeasureTheory ProbabilityTheory Filter
section MeasurableSpace
variable {E : Type*}
variable [MeasurableSpace E]
/-- The normalized sum of `f` is orthogonal to every coordinate `g(x_i)` when `f` and `g` are
centered and `∫ f g dμ = 0`. -/
theorem solution
    (μ : Measure E) [IsProbabilityMeasure μ] (f g : E → ℝ)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) (hg0 : ∫ x, g x ∂μ = 0)
    (hfg0 : ∫ x, f x * g x ∂μ = 0) (N : ℕ) (hN : 0 < N) (i : Fin N) :
    Integrable (fun x : Fin N → E => ((∑ k, f (x k)) / Real.sqrt N) * g (x i))
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → E, ((∑ k, f (x k)) / Real.sqrt N) * g (x i)
        ∂(Measure.pi (fun _ : Fin N => μ))) = 0 := by
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  let R : (Fin N → E) → ℝ := fun x => ∑ k, f (x k) * g (x i)
  have hprod (k : Fin N) : Integrable (fun x : Fin N → E => f (x k) * g (x i)) ν :=
    (FunctionalInequalities.Probability.integral_mul_comp_eval_pi_readable μ f g hf2 hg2 N k i).1
  have hRint : Integrable R ν :=
    integrable_finsetSum Finset.univ (fun k _ => hprod k)
  have hzero (k : Fin N) : (∫ x : Fin N → E, f (x k) * g (x i) ∂ν) = 0 := by
    rw [(FunctionalInequalities.Probability.integral_mul_comp_eval_pi_readable μ f g hf2 hg2 N k i).2]
    by_cases hki : k = i
    · rw [if_pos hki, hfg0]
    · rw [if_neg hki, hf0, hg0]
      simp
  have hR0 : (∫ x, R x ∂ν) = 0 := by
    calc
      _ = ∑ k : Fin N, ∫ x, f (x k) * g (x i) ∂ν :=
        integral_finsetSum _ (fun k _ => hprod k)
      _ = 0 := by simp_rw [hzero]; simp
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  have heq (x : Fin N → E) :
      ((∑ k, f (x k)) / Real.sqrt N) * g (x i) = R x / Real.sqrt N := by
    dsimp [R]
    rw [← Finset.sum_mul]
    field_simp [hsqrt]
  have heqfun : (fun x : Fin N → E => ((∑ k, f (x k)) / Real.sqrt N) * g (x i)) =
      (fun x => R x / Real.sqrt N) := funext heq
  rw [heqfun]
  refine ⟨hRint.div_const _, ?_⟩
  rw [integral_div, hR0]
  simp
