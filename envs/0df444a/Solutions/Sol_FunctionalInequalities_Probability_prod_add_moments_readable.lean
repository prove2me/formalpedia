-- Prove2me | solution 1 for FunctionalInequalities.Probability.prod_add_moments_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:43:41.96599+00:00
-- url     : https://prove2.me/submissions/7e0f59f1-891a-4b40-9c6c-ae4766579169

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Product

noncomputable section
open MeasureTheory ProbabilityTheory Filter
section MeasurableSpace
variable {A B : Type*}
variable [MeasurableSpace A] [MeasurableSpace B]
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
