-- Prove2me | solution 1 for Continuous.nonnegative_integral_vanishes_iff_function_vanishes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:37.283608+00:00
-- url     : https://prove2.me/submissions/503eac97-4b10-4888-891f-d101f24d7dd0

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
namespace Continuous
theorem _root_.solution {f : E → ℝ} (hf₁ : Continuous f)
  (hf₂ : Integrable f) (hnn : ∀ x, 0 ≤ f x) : ∫ (v : E), f v = 0 ↔ f = 0 := by
  constructor
  · intro hzero
    funext x
    change f x = 0
    by_contra hx
    have hopen : IsOpen (Function.support f) := by
      exact (isOpen_ne : IsOpen {y : ℝ | y ≠ 0}).preimage hf₁
    have hmeasure : 0 < volume (Function.support f) :=
      hopen.measure_pos volume ⟨x, hx⟩
    have hpositive : 0 < ∫ v : E, f v :=
      (integral_pos_iff_support_of_nonneg hnn hf₂).2 hmeasure
    linarith
  · intro hzero
    simp [hzero]
end Continuous
