-- Prove2me | solution 1 for FunctionalInequalities.Probability.integral_prod_add_mul_eq_zero_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:59:23.900991+00:00
-- url     : https://prove2.me/submissions/9d0ef6b8-2874-482c-be2e-84844c79c3f9

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
