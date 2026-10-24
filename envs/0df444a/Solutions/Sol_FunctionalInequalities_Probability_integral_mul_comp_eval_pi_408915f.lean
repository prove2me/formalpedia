-- Prove2me | solution 1 for FunctionalInequalities.Probability.integral_mul_comp_eval_pi_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:59:10.880655+00:00
-- url     : https://prove2.me/submissions/fbbf247c-13a9-44e0-9fe5-556fc7ccaaa8

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
/-- A coordinate of `μ^N` has law `μ`. -/
theorem FunctionalInequalities.Probability.integral_comp_eval_pi
    (μ : Measure E) [IsProbabilityMeasure μ] (a : E → ℝ)
    (ha : AEStronglyMeasurable a μ) (N : ℕ) (i : Fin N) :
    (∫ x : Fin N → E, a (x i) ∂(Measure.pi (fun _ : Fin N => μ))) = ∫ x, a x ∂μ := by
  have he := measurePreserving_eval (fun _ : Fin N => μ) i
  have hm : AEStronglyMeasurable a
      ((Measure.pi (fun _ : Fin N => μ)).map (Function.eval i)) := by
    rw [he.map_eq]
    exact ha
  calc
    _ = ∫ x, a x ∂((Measure.pi (fun _ : Fin N => μ)).map (Function.eval i)) :=
      (integral_map he.measurable.aemeasurable hm).symm
    _ = ∫ x, a x ∂μ := by rw [he.map_eq]
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
/-- **Products of coordinates.** For `f, g ∈ L²(μ)`, `∫ f(x_i) g(x_j) dμ^N` is `∫ f g dμ` when
`i = j` and `(∫ f dμ)(∫ g dμ)` otherwise. -/
theorem solution
    (μ : Measure E) [IsProbabilityMeasure μ] (f g : E → ℝ)
    (hf2 : MemLp f 2 μ) (hg2 : MemLp g 2 μ) (N : ℕ) (i j : Fin N) :
    Integrable (fun x : Fin N → E => f (x i) * g (x j))
      (Measure.pi (fun _ : Fin N => μ)) ∧
      (∫ x : Fin N → E, f (x i) * g (x j) ∂(Measure.pi (fun _ : Fin N => μ))) =
        if i = j then ∫ x, f x * g x ∂μ
          else (∫ x, f x ∂μ) * (∫ x, g x ∂μ) := by
  classical
  let ν := Measure.pi (fun _ : Fin N => μ)
  have hF2 : MemLp (fun x : Fin N → E => f (x i)) 2 ν :=
    hf2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) i)
  have hG2 : MemLp (fun x : Fin N → E => g (x j)) 2 ν :=
    hg2.comp_measurePreserving (measurePreserving_eval (fun _ : Fin N => μ) j)
  have hprod : MemLp (fun x : Fin N → E => f (x i) * g (x j)) 1 ν :=
    hG2.mul' hF2
  refine ⟨hprod.integrable le_rfl, ?_⟩
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact FunctionalInequalities.Probability.integral_comp_eval_pi μ (fun x => f x * g x)
      (hf2.aestronglyMeasurable.mul hg2.aestronglyMeasurable) N i
  · rw [if_neg hij]
    let X : Fin N → E → ℝ := fun k => if k = i then f else g
    have hX : ∀ k : Fin N, AEMeasurable (X k) μ := by
      intro k
      by_cases hk : k = i
      · simpa [X, hk] using hf2.aemeasurable
      · simpa [X, hk] using hg2.aemeasurable
    have hind : iIndepFun (fun k (x : Fin N → E) => X k (x k)) ν :=
      iIndepFun_pi (μ := fun _ : Fin N => μ) hX
    have hfg : IndepFun (fun x : Fin N → E => f (x i))
        (fun x : Fin N → E => g (x j)) ν := by
      have hji : j ≠ i := fun h => hij h.symm
      simpa [X, hji] using hind.indepFun hij
    have h := hfg.integral_mul_eq_mul_integral
      hF2.aestronglyMeasurable hG2.aestronglyMeasurable
    simp only [Pi.mul_apply] at h
    rw [FunctionalInequalities.Probability.integral_comp_eval_pi μ f hf2.aestronglyMeasurable N i,
      FunctionalInequalities.Probability.integral_comp_eval_pi μ g hg2.aestronglyMeasurable N j] at h
    exact h
