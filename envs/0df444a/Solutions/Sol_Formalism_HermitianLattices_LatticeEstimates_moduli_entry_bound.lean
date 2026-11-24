-- Prove2me | solution 1 for Formalism.HermitianLattices.LatticeEstimates.moduli_entry_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:43.894009+00:00
-- url     : https://prove2.me/submissions/cf44fbbb-a77d-4b16-b426-b569c39d923f

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
theorem _root_.solution : Ms_entry := by
  intro f p q z R2 hp hq hz hP hQ
  have h0 : 0 ≤ ∑ τ, p τ := Finset.sum_nonneg fun τ _ => hp τ
  have h0' : 0 ≤ ∑ τ, q τ := Finset.sum_nonneg fun τ _ => hq τ
  calc ∑ τ, ‖z τ‖ ^ 2 ≤ ∑ τ, p τ * q τ := Finset.sum_le_sum fun τ _ => hz τ
    _ ≤ ∑ τ, p τ * ∑ σ, q σ := Finset.sum_le_sum fun τ _ =>
        mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun σ _ => hq σ) (Finset.mem_univ τ)) (hp τ)
    _ = (∑ τ, p τ) * ∑ σ, q σ := by rw [Finset.sum_mul]
    _ ≤ R2 * R2 := mul_le_mul hP hQ h0' (h0.trans hP)
    _ = R2 ^ 2 := by ring
end Formalism.HermitianLattices.LatticeEstimates
