-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_finite_exponential_generator_linear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:02:24.736596+00:00
-- url     : https://prove2.me/submissions/8269417c-71e5-4d12-9331-5b342743e07a

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FunProp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levyWeight_integrable
import Theorems.Thm_AvramDividend_Classical_levy_exponential_generatorIntegrable_of_moment
import Theorems.Thm_AvramDividend_Classical_levy_generatorIntegrable_const_mul
import Theorems.Thm_AvramDividend_Classical_levy_generator_const_mul
import Theorems.Thm_AvramDividend_Classical_levy_generator_add_of_jet_additive
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Finite signed exponential test families are in the exact Lévy generator domain,
with the full compensated generator acting linearly. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (coeff rate : ι → ℝ) (hrate : ∀ i ∈ s, 0 ≤ rate i)
    (x : ℝ) :
    X.GeneratorIntegrable
      (fun z : ℝ => ∑ i ∈ s, coeff i * Real.exp (rate i * z)) x ∧
    X.generator
      (fun z : ℝ => ∑ i ∈ s, coeff i * Real.exp (rate i * z)) x =
      ∑ i ∈ s, coeff i *
        X.generator (fun z : ℝ => Real.exp (rate i * z)) x := by
  classical
  have hweight : IntegrableOn
      (fun y : ℝ => min 1 (y ^ 2)) (Iio (0 : ℝ)) X.ν :=
    (levyWeight_integrable X).integrableOn
  have hsmooth (u : Finset ι) :
      ContDiff ℝ (2 : ℕ)
        (fun z : ℝ => ∑ j ∈ u, coeff j * Real.exp (rate j * z)) := by
    induction u using Finset.induction_on with
    | empty =>
        simpa using (contDiff_const :
          ContDiff ℝ (2 : ℕ) (fun _ : ℝ => (0 : ℝ)))
    | @insert i u hnot ih =>
        have hsingle : ContDiff ℝ (2 : ℕ)
            (fun z : ℝ => coeff i * Real.exp (rate i * z)) := by
          fun_prop
        simpa only [Finset.sum_insert hnot] using hsingle.add ih
  have hfinite :
      ∀ u : Finset ι, (∀ i ∈ u, 0 ≤ rate i) →
        X.GeneratorIntegrable
          (fun z : ℝ => ∑ i ∈ u, coeff i * Real.exp (rate i * z)) x ∧
        X.generator
          (fun z : ℝ => ∑ i ∈ u, coeff i * Real.exp (rate i * z)) x =
          ∑ i ∈ u, coeff i *
            X.generator (fun z : ℝ => Real.exp (rate i * z)) x := by
    intro u
    induction u using Finset.induction_on with
    | empty =>
        intro _
        have hbase := levy_exponential_generatorIntegrable_of_moment
          X 0 x (le_refl (0 : ℝ)) hweight
        have hzero := levy_generatorIntegrable_const_mul
          X (fun z : ℝ => Real.exp (0 * z)) 0 x hbase
        have hzeroGen := levy_generator_const_mul
          X (fun z : ℝ => Real.exp (0 * z)) 0 x
        constructor
        · simpa only [Finset.sum_empty, zero_mul] using hzero
        · simpa only [Finset.sum_empty, zero_mul] using hzeroGen
    | @insert i u hnot ih =>
        intro hu
        have hi : 0 ≤ rate i :=
          hu i (Finset.mem_insert_self i u)
        have hrest : ∀ j ∈ u, 0 ≤ rate j := by
          intro j hj
          exact hu j (Finset.mem_insert_of_mem hj)
        obtain ⟨htail, hgenTail⟩ := ih hrest
        have hsingle0 := levy_exponential_generatorIntegrable_of_moment
          X (rate i) x hi hweight
        have hsingle := levy_generatorIntegrable_const_mul
          X (fun z : ℝ => Real.exp (rate i * z)) (coeff i) x hsingle0
        have hfirst :
            deriv (fun z : ℝ => coeff i * Real.exp (rate i * z) +
              ∑ j ∈ u, coeff j * Real.exp (rate j * z)) x =
            deriv (fun z : ℝ => coeff i * Real.exp (rate i * z)) x +
            deriv (fun z : ℝ => ∑ j ∈ u, coeff j * Real.exp (rate j * z)) x := by
          have hfa : DifferentiableAt ℝ
              (fun z : ℝ => coeff i * Real.exp (rate i * z)) x := by
            fun_prop
          have hfb : DifferentiableAt ℝ
              (fun z : ℝ => ∑ j ∈ u, coeff j * Real.exp (rate j * z)) x :=
            ((hsmooth u).contDiffAt).differentiableAt (by norm_num)
          exact deriv_add hfa hfb
        have hsecond :
            iteratedDeriv 2 (fun z : ℝ => coeff i * Real.exp (rate i * z) +
              ∑ j ∈ u, coeff j * Real.exp (rate j * z)) x =
            iteratedDeriv 2 (fun z : ℝ => coeff i * Real.exp (rate i * z)) x +
            iteratedDeriv 2 (fun z : ℝ => ∑ j ∈ u, coeff j * Real.exp (rate j * z)) x := by
          have hfa : ContDiffAt ℝ (2 : ℕ)
              (fun z : ℝ => coeff i * Real.exp (rate i * z)) x := by
            fun_prop
          exact iteratedDeriv_add hfa (hsmooth u).contDiffAt
        obtain ⟨hint, hgen⟩ := levy_generator_add_of_jet_additive X
          (fun z : ℝ => coeff i * Real.exp (rate i * z))
          (fun z : ℝ => ∑ j ∈ u, coeff j * Real.exp (rate j * z))
          x hsingle htail hfirst hsecond
        constructor
        · convert hint using 1
          ext z
          simp only [Finset.sum_insert hnot]
        · calc
            X.generator
              (fun z : ℝ => ∑ j ∈ insert i u,
                coeff j * Real.exp (rate j * z)) x =
              X.generator
                (fun z : ℝ => coeff i * Real.exp (rate i * z) +
                  ∑ j ∈ u, coeff j * Real.exp (rate j * z)) x := by
                congr 1
                funext z
                simp only [Finset.sum_insert hnot]
            _ = X.generator
                  (fun z : ℝ => coeff i * Real.exp (rate i * z)) x +
                X.generator
                  (fun z : ℝ => ∑ j ∈ u, coeff j * Real.exp (rate j * z)) x :=
                  hgen
            _ = coeff i * X.generator
                  (fun z : ℝ => Real.exp (rate i * z)) x +
                ∑ j ∈ u, coeff j *
                  X.generator (fun z : ℝ => Real.exp (rate j * z)) x := by
                  rw [levy_generator_const_mul, hgenTail]
            _ = ∑ j ∈ insert i u, coeff j *
                  X.generator (fun z : ℝ => Real.exp (rate j * z)) x := by
                  simp only [Finset.sum_insert hnot]
  exact hfinite s hrate
