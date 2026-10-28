-- Prove2me | solution 1 for FunctionalInequalities.Probability.integral_prod_add_mul_eq_zero_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:43:54.590249+00:00
-- url     : https://prove2.me/submissions/78faefd6-39fa-48cc-8015-f08a7ebc21d6

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Product

noncomputable section
open MeasureTheory ProbabilityTheory Filter
section MeasurableSpace
variable {A B : Type*}
variable [MeasurableSpace A] [MeasurableSpace B]
/-- Under `μ ⊗ ν`, `∫ (X + Y) Z = 0` when `∫ X Z dμ = 0` and `Y` is centered. -/
theorem solution
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X Z : A → ℝ) (Y : B → ℝ)
    (hX2 : MemLp X 2 μ) (hZ2 : MemLp Z 2 μ) (hY2 : MemLp Y 2 ν)
    (hXZ0 : ∫ x, X x * Z x ∂μ = 0) (hY0 : ∫ y, Y y ∂ν = 0) :
    Integrable (fun p : A × B => (X p.1 + Y p.2) * Z p.1) (μ.prod ν) ∧
      (∫ p : A × B, (X p.1 + Y p.2) * Z p.1 ∂(μ.prod ν)) = 0 := by
  have hXfirst : MemLp (fun p : A × B => X p.1) 2 (μ.prod ν) := hX2.comp_fst ν
  have hZfirst : MemLp (fun p : A × B => Z p.1) 2 (μ.prod ν) := hZ2.comp_fst ν
  have hYsecond : MemLp (fun p : A × B => Y p.2) 2 (μ.prod ν) := hY2.comp_snd μ
  have hXZ : MemLp (fun p : A × B => X p.1 * Z p.1) 1 (μ.prod ν) :=
    hZfirst.mul' hXfirst
  have hZY : MemLp (fun p : A × B => Z p.1 * Y p.2) 1 (μ.prod ν) :=
    hYsecond.mul' hZfirst
  have hmixed : MemLp (fun p : A × B => (X p.1 + Y p.2) * Z p.1) 1 (μ.prod ν) :=
    hZfirst.mul' (hXfirst.add hYsecond)
  refine ⟨hmixed.integrable le_rfl, ?_⟩
  have heq : (fun p : A × B => (X p.1 + Y p.2) * Z p.1) =
      (fun p => X p.1 * Z p.1 + Z p.1 * Y p.2) := by
    funext p
    ring
  rw [heq, integral_add (hXZ.integrable le_rfl) (hZY.integrable le_rfl),
    integral_fun_fst (fun x => X x * Z x), integral_prod_mul Z Y, hXZ0, hY0]
  simp
