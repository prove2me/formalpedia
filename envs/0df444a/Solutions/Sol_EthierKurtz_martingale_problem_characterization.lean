-- Prove2me | solution 1 for EthierKurtz.martingale_problem_characterization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:54:00.549365+00:00
-- url     : https://prove2.me/submissions/635a3f34-3d7b-478b-be72-0f008d3474b6

import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem
import Theorems.Thm_EthierKurtz_semigroup_generator_from_range_conditions
import Theorems.Thm_EthierKurtz_martingale_solution_has_semigroup_conditional_expectation
import Theorems.Thm_EthierKurtz_martingale_solution_is_markov
import Theorems.Thm_EthierKurtz_martingale_problem_determines_finite_dimensional_distributions

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology

open EthierKurtz

variable {E Ω Ω' : Type*} [MeasurableSpace E] [MeasurableSpace Ω] [MeasurableSpace Ω']

theorem solution
    [MetricSpace E] [BorelSpace E] [SeparableSpace E]
    (A A' : Submodule ℝ (UniformBoundedFunction E × UniformBoundedFunction E))
    (hAmeas : ∀ fg ∈ A, Measurable (fg.1 : E → ℝ) ∧ Measurable (fg.2 : E → ℝ))
    (hsub : A' ≤ A)
    (hdiss : ∀ fg ∈ A, ∀ a : ℝ, 0 < a → a * ‖fg.1‖ ≤ ‖a • fg.1 - fg.2‖)
    (L : Submodule ℝ (UniformBoundedFunction E))
    (hrange : ∃ a : ℝ, 0 < a ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        a • fg.1 - fg.2) '' (A' : Set _)) = (L : Set _) ∧
      closure ((fun fg : UniformBoundedFunction E × UniformBoundedFunction E =>
        fg.1) '' (A' : Set _)) = (L : Set (UniformBoundedFunction E)))
    (hsep : ∀ (ν₁ ν₂ : Measure E), IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ →
      (∀ f : L, (∫ x, (f.val : E → ℝ) x ∂ν₁) = ∫ x, (f.val : E → ℝ) x ∂ν₂) →
      ν₁ = ν₂)
    (μ : Measure E) [IsProbabilityMeasure μ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → E) (hX : SolvesMartingaleProblem A μ P X) :
    (∃ T : ℝ → L →L[ℝ] L,
      (T 0 = ContinuousLinearMap.id ℝ L ∧
       (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t)) ∧
       (∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ 1) ∧
       (∀ f : L, Tendsto (fun t : ℝ => T t f) (𝓝[>] (0 : ℝ)) (𝓝 f))) ∧
      (∀ f g : L,
        Tendsto (fun t : ℝ => t⁻¹ • (T t f - f)) (𝓝[>] (0 : ℝ)) (𝓝 g) ↔
          (f.val, g.val) ∈ closure (A' : Set _)) ∧
      (∀ (s t : ℝ≥0) (f : L),
        P[fun ω => (f.val : E → ℝ) (X (s + t) ω) | processPast X s] =ᵐ[P]
          fun ω => ((T (t : ℝ) f).val : E → ℝ) (X s ω))) ∧
    (∀ (s t : ℝ≥0) (f : UniformBoundedFunction E), Measurable (f : E → ℝ) →
      P[fun ω => f (X (s + t) ω) | processPast X s] =ᵐ[P]
        P[fun ω => f (X (s + t) ω) |
          MeasurableSpace.comap (X s) ‹MeasurableSpace E›]) ∧
    (∀ (Q : Measure Ω'), IsProbabilityMeasure Q → ∀ Y : ℝ≥0 → Ω' → E,
      SolvesMartingaleProblem A μ Q Y → ∀ (n : ℕ) (t : Fin n → ℝ≥0),
        Measure.map (fun ω i => X (t i) ω) P =
          Measure.map (fun ω i => Y (t i) ω) Q) := by
  obtain ⟨T, hT, hTgen⟩ :=
    EthierKurtz.semigroup_generator_from_range_conditions
      A A' hsub hdiss L hrange
  have hcond :=
    EthierKurtz.martingale_solution_has_semigroup_conditional_expectation
      (E := E) (Ω := Ω) (Ω' := Ω)
      A A' hAmeas hsub hdiss L hrange hsep μ P X hX T hT hTgen
  have hmarkov :=
    EthierKurtz.martingale_solution_is_markov
      (E := E) (Ω := Ω) (Ω' := Ω)
      A A' hAmeas hsub hdiss L hrange hsep μ P X hX
  have hfinite :=
    EthierKurtz.martingale_problem_determines_finite_dimensional_distributions
      (E := E) (Ω := Ω) (Ω' := Ω')
      A A' hAmeas hsub hdiss L hrange hsep μ P X hX
  exact ⟨⟨T, hT, hTgen, hcond⟩, hmarkov, hfinite⟩
