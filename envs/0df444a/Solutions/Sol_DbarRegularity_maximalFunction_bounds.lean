-- Prove2me | solution 1 for DbarRegularity.maximalFunction_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-11T23:08:35.03766+00:00
-- url     : https://prove2.me/submissions/d564cb45-7de1-4dc9-8349-00086c7345ea

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Theorems.Thm_DbarRegularity_maximalFunction_ae_lt_top
import Theorems.Thm_DbarRegularity_maximalFunction_weakType_one
import Theorems.Thm_DbarRegularity_maximalFunction_strongType



namespace DbarRegularity

open MeasureTheory
open scoped ENNReal NNReal

theorem maximalFunction_bounds' (d : ℕ) :
    (∀ p : ℝ≥0∞, 1 ≤ p → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f p →
      ∀ᵐ x, maximalFunction f x < ⊤) ∧
    (∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, Integrable f → ∀ α : ℝ≥0, 0 < α →
      volume {x | (α : ℝ≥0∞) < maximalFunction f x} ≤ (A : ℝ≥0∞) / α * ∫⁻ x, ‖f x‖ₑ) ∧
    (∀ p : ℝ≥0∞, 1 < p → ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f p →
      MemLp (maximalFunction f) p ∧
        eLpNorm (maximalFunction f) p volume ≤ A * eLpNorm f p volume) := by
  refine ⟨maximalFunction_ae_lt_top d, ⟨5 ^ d, fun f _ α hα => ?_⟩, maximalFunction_strongType d⟩
  have h := maximalFunction_weakType_one d f α hα
  push_cast
  exact h

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

theorem solution (d : ℕ) :
    (∀ p : ℝ≥0∞, 1 ≤ p → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f p →
      ∀ᵐ x, maximalFunction f x < ⊤) ∧
    (∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, Integrable f → ∀ α : ℝ≥0, 0 < α →
      volume {x | (α : ℝ≥0∞) < maximalFunction f x} ≤ (A : ℝ≥0∞) / α * ∫⁻ x, ‖f x‖ₑ) ∧
    (∀ p : ℝ≥0∞, 1 < p → ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f p →
      MemLp (maximalFunction f) p ∧
        eLpNorm (maximalFunction f) p volume ≤ A * eLpNorm f p volume) :=
  maximalFunction_bounds' d
