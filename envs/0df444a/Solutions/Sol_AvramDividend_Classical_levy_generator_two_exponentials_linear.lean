-- Prove2me | solution 1 for AvramDividend.Classical.levy_generator_two_exponentials_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T23:01:03.094878+00:00
-- url     : https://prove2.me/submissions/91a5a854-41d4-42f1-ac6b-2c8caae5888c

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FunProp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyWeight_integrable
import Theorems.Thm_AvramDividend_Classical_levy_exponential_generatorIntegrable_of_moment
import Theorems.Thm_AvramDividend_Classical_levy_generatorIntegrable_const_mul
import Theorems.Thm_AvramDividend_Classical_levy_generator_const_mul
import Theorems.Thm_AvramDividend_Classical_levy_generator_add_of_jet_additive
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Generator domain closure and two-term exponential linearity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b θ φ x : ℝ) (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) :
    X.GeneratorIntegrable
      (fun z : ℝ => a * Real.exp (θ * z) + b * Real.exp (φ * z)) x ∧
    X.generator
      (fun z : ℝ => a * Real.exp (θ * z) + b * Real.exp (φ * z)) x =
      a * X.generator (fun z : ℝ => Real.exp (θ * z)) x +
      b * X.generator (fun z : ℝ => Real.exp (φ * z)) x := by
  have hweight : IntegrableOn
      (fun y : ℝ => min 1 (y ^ 2)) (Iio (0 : ℝ)) X.ν :=
    (levyWeight_integrable X).integrableOn
  have hθint :=
    levy_exponential_generatorIntegrable_of_moment X θ x hθ hweight
  have hφint :=
    levy_exponential_generatorIntegrable_of_moment X φ x hφ hweight
  have ha :=
    levy_generatorIntegrable_const_mul X
      (fun z : ℝ => Real.exp (θ * z)) a x hθint
  have hb :=
    levy_generatorIntegrable_const_mul X
      (fun z : ℝ => Real.exp (φ * z)) b x hφint
  have hfirst :
      deriv (fun z : ℝ => a * Real.exp (θ * z) +
        b * Real.exp (φ * z)) x =
        deriv (fun z : ℝ => a * Real.exp (θ * z)) x +
        deriv (fun z : ℝ => b * Real.exp (φ * z)) x := by
    have hfa : DifferentiableAt ℝ (fun z : ℝ => a * Real.exp (θ * z)) x := by
      fun_prop
    have hfb : DifferentiableAt ℝ (fun z : ℝ => b * Real.exp (φ * z)) x := by
      fun_prop
    exact deriv_add hfa hfb
  have hsecond :
      iteratedDeriv 2 (fun z : ℝ =>
        a * Real.exp (θ * z) + b * Real.exp (φ * z)) x =
        iteratedDeriv 2 (fun z : ℝ => a * Real.exp (θ * z)) x +
        iteratedDeriv 2 (fun z : ℝ => b * Real.exp (φ * z)) x := by
    have hfa : ContDiffAt ℝ (2 : ℕ) (fun z : ℝ =>
        a * Real.exp (θ * z)) x := by
      fun_prop
    have hfb : ContDiffAt ℝ (2 : ℕ) (fun z : ℝ =>
        b * Real.exp (φ * z)) x := by
      fun_prop
    exact iteratedDeriv_add hfa hfb
  obtain ⟨hint, hgen⟩ :=
    levy_generator_add_of_jet_additive X
      (fun z : ℝ => a * Real.exp (θ * z))
      (fun z : ℝ => b * Real.exp (φ * z))
      x ha hb hfirst hsecond
  refine ⟨hint, ?_⟩
  simpa only [levy_generator_const_mul] using hgen
