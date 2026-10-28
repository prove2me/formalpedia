-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_positive_root_C1_volterra_unique_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:24:00.624017+00:00
-- url     : https://prove2.me/submissions/5fe4cd1b-777c-4fc8-b6f7-f25683e39d59

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_gaussian
import Theorems.Thm_AvramDividend_Classical_gaussian_esscher_volterra_C1_unique
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q ∧
      ContDiffOn ℝ 1 (fun x : ℝ => Real.exp (-(φ * x)) * W x) (Ioi (0 : ℝ)) ∧
      ∃ (a β : ℝ) (K : ℝ → ℝ),
        0 < a ∧ IntegrableOn K (Ioi (0 : ℝ)) volume ∧
        (∀ x : ℝ, 0 < x →
          a * (fun x : ℝ => Real.exp (-(φ * x)) * W x) x +
            (∫ s in Ioc (0 : ℝ) x,
              (β + K (x - s)) * (fun x : ℝ => Real.exp (-(φ * x)) * W x) s ∂volume) = x) ∧
        (∀ G : ℝ → ℝ,
          ContinuousOn G (Ioi (0 : ℝ)) →
          (∀ R : ℝ, 0 < R →
            ∃ C : ℝ, ∀ x : ℝ, x ∈ Ioc (0 : ℝ) R → |G x| ≤ C) →
          (∀ x : ℝ, 0 < x →
            a * G x +
              (∫ s in Ioc (0 : ℝ) x,
                (β + K (x - s)) * G s ∂volume) = x) →
          ∀ x : ℝ, 0 < x → G x = (fun x : ℝ => Real.exp (-(φ * x)) * W x) x) := by
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_gaussian X q hq hσ
  have hV : ∀ x : ℝ, 0 < x →
      (fun x : ℝ => Real.exp (-(φ * x)) * W x) x = Real.exp (-(φ * x)) * W x := by
    intro x hx
    rfl
  obtain ⟨hC1, a, β, K, ha, hKi, hEq, hUnique⟩ :=
    gaussian_esscher_volterra_C1_unique
      X q hq W hW hσ φ hφ hroot (fun x : ℝ => Real.exp (-(φ * x)) * W x) hV
  exact ⟨φ, hφ, hroot, hC1, a, β, K, ha, hKi, hEq, hUnique⟩
