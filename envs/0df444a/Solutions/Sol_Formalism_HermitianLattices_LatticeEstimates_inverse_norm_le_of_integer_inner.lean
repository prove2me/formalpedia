-- Prove2me | solution 1 for Formalism.HermitianLattices.LatticeEstimates.inverse_norm_le_of_integer_inner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:43.694611+00:00
-- url     : https://prove2.me/submissions/80dd6871-0ef4-4f52-a09e-462afbbe1895

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InverseNormLeOfIntegerInner
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LatticeEstimates
open Finset MeasureTheory Matrix Real
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (Interlace B0 len)
open scoped ComplexOrder
namespace Formalism.HermitianLattices.LatticeEstimates
theorem _root_.solution : InverseNormLeOfIntegerInner := by
  intro V _ _ x φ z hz h
  have h1 : (1:ℝ) ≤ ‖inner ℂ x φ‖ := by
    rw [h, Complex.norm_intCast]; exact_mod_cast Int.one_le_abs hz
  have h2 := norm_inner_le_norm (𝕜 := ℂ) x φ
  have hx : 0 < ‖x‖ := by
    rcases (norm_nonneg x).lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at h2; linarith
  rw [div_le_iff₀ hx]; linarith [mul_comm ‖x‖ ‖φ‖]
end Formalism.HermitianLattices.LatticeEstimates
