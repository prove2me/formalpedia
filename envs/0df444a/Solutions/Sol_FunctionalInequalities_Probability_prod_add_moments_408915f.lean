-- Prove2me | solution 1 for FunctionalInequalities.Probability.prod_add_moments_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:58:56.413867+00:00
-- url     : https://prove2.me/submissions/f5020516-8ddb-4c2f-a0b1-0291cc6ddc65

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
variable {A B : Type*}
variable [MeasurableSpace A] [MeasurableSpace B]
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities.Probability in
/-- **Independent sums.** Under `μ ⊗ ν`, centered `X ∈ L²(μ)` and `Y ∈ L²(ν)` give a centered
sum `X + Y` with second moment `∫ X² dμ + ∫ Y² dν`. -/
theorem solution
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : A → ℝ) (Y : B → ℝ) (hX2 : MemLp X 2 μ) (hY2 : MemLp Y 2 ν)
    (hX0 : ∫ x, X x ∂μ = 0) (hY0 : ∫ y, Y y ∂ν = 0) :
    MemLp (fun p : A × B => X p.1 + Y p.2) 2 (μ.prod ν) ∧
      (∫ p : A × B, X p.1 + Y p.2 ∂(μ.prod ν)) = 0 ∧
      (∫ p : A × B, (X p.1 + Y p.2) ^ 2 ∂(μ.prod ν)) =
        (∫ x, X x ^ 2 ∂μ) + (∫ y, Y y ^ 2 ∂ν) := by
  have hXfirst : MemLp (fun p : A × B => X p.1) 2 (μ.prod ν) := hX2.comp_fst ν
  have hYsecond : MemLp (fun p : A × B => Y p.2) 2 (μ.prod ν) := hY2.comp_snd μ
  have hsum2 : MemLp (fun p : A × B => X p.1 + Y p.2) 2 (μ.prod ν) :=
    hXfirst.add hYsecond
  have hsum0 : (∫ p : A × B, X p.1 + Y p.2 ∂(μ.prod ν)) = 0 := by
    rw [integral_add (hXfirst.integrable one_le_two) (hYsecond.integrable one_le_two),
      integral_fun_fst X, integral_fun_snd Y, hX0, hY0]
    simp
  refine ⟨hsum2, hsum0, ?_⟩
  have hv := variance_add_prod hX2 hY2
  rw [variance_eq_sub hsum2, hsum0, variance_eq_sub hX2, variance_eq_sub hY2,
    hX0, hY0] at hv
  simpa only [Pi.pow_apply, zero_pow (by norm_num : 2 ≠ 0), sub_zero] using hv
