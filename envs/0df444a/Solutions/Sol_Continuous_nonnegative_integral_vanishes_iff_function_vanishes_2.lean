-- Prove2me | solution 2 for Continuous.nonnegative_integral_vanishes_iff_function_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:35:37.14456+00:00
-- url     : https://prove2.me/submissions/1130e9ce-e790-4e6c-9420-fa364551a18d

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {d : ℕ} [Fact (0 < d)]
variable (Λ : Submodule ℤ (EuclideanSpace ℝ (Fin d))) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
noncomputable section
open scoped BigOperators FourierTransform
open MeasureTheory Filter
variable {E : Type*} [NormedAddCommGroup E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [MeasureSpace E] [BorelSpace E]
variable [(volume : Measure E).IsAddLeftInvariant] [(volume : Measure E).Regular]
  [NeZero (volume : Measure E)]


theorem solution {f : E → ℝ} (hf₁ : Continuous f)
  (hf₂ : Integrable f) (hnn : ∀ x, 0 ≤ f x) : ∫ (v : E), f v = 0 ↔ f = 0 := by
  constructor
  · intro h
    have hae := (integral_eq_zero_iff_of_nonneg (fun x => hnn x) hf₂).mp h
    exact (hf₁.ae_eq_iff_eq volume continuous_zero).mp hae
  · rintro rfl
    simp

