-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.weight_change_formula
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:47.401889+00:00
-- url     : https://prove2.me/submissions/cd4051cb-acd3-431e-b6e1-d3f0091ae817

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SquareMomentFromBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : Weight_change := by
  intro X X' V V' _ _ _ _ K u u' D B hD hB hu hu'
  have hDpos : 0 < D := by linarith
  have A1 : ∀ (Y : Type) [Fintype Y] (w : Y → ℝ) (a : Y → ℝ), (∀ y, 1 / D ≤ w y ∧ w y ≤ 1) →
      (∀ y, 0 ≤ a y) → ∑ y, w y * a y ≤ ∑ y, a y ∧ ∑ y, a y ≤ D * ∑ y, w y * a y := by
    intro Y _ w a hw ha
    constructor
    · exact Finset.sum_le_sum fun y _ => by
        have := (hw y).2
        nlinarith [ha y]
    · rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun y _ => by
        have h1 := (hw y).1
        rw [div_le_iff₀ hDpos] at h1
        nlinarith [ha y]
  refine ⟨fun hK φ => ?_, fun hK φ => ?_⟩
  · obtain ⟨h1, _⟩ := A1 X' u' (fun x => ‖K φ x‖ ^ 2) hu' (fun x => by positivity)
    obtain ⟨_, h2⟩ := A1 X u (fun x => ‖φ x‖ ^ 2) hu (fun x => by positivity)
    calc ∑ x, u' x * ‖K φ x‖ ^ 2 ≤ ∑ x, ‖K φ x‖ ^ 2 := h1
      _ ≤ B * ∑ x, ‖φ x‖ ^ 2 := hK φ
      _ ≤ B * (D * ∑ x, u x * ‖φ x‖ ^ 2) := mul_le_mul_of_nonneg_left h2 hB
      _ = (B * D) * ∑ x, u x * ‖φ x‖ ^ 2 := by ring
  · obtain ⟨_, h1⟩ := A1 X' u' (fun x => ‖K φ x‖ ^ 2) hu' (fun x => by positivity)
    obtain ⟨h2, _⟩ := A1 X u (fun x => ‖φ x‖ ^ 2) hu (fun x => by positivity)
    calc ∑ x, ‖K φ x‖ ^ 2 ≤ D * ∑ x, u' x * ‖K φ x‖ ^ 2 := h1
      _ ≤ D * (B * ∑ x, u x * ‖φ x‖ ^ 2) := mul_le_mul_of_nonneg_left (hK φ) hDpos.le
      _ ≤ D * (B * ∑ x, ‖φ x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hB) hDpos.le
      _ = (B * D) * ∑ x, ‖φ x‖ ^ 2 := by ring
end Formalism.HermitianLattices.TraceIntegrality
