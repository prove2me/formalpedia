-- Prove2me | solution 1 for Formalism.HermitianLattices.LatticeEstimates.fourth_zeta_arithmetic_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:43.352805+00:00
-- url     : https://prove2.me/submissions/13bc2396-0e7a-448d-92cc-92318c152446

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InverseNormLeOfIntegerInner
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Theorems.Thm_Formalism_HermitianLattices_LatticeEstimates_weight_positive_part_nonneg

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
theorem _root_.solution : MuMaxBoundOfAntitoneWeight := by
  intro κ lam muMax dmin cc hA hcc hd hdm hc hmu
  have hk : (0:ℝ) < (κ : ℝ) + 1 := by positivity
  have hw := weight_positive_part_nonneg lam hA
  have e1 : -Real.log dmin ≤ (wt (plus lam) : ℝ) * Real.log ((κ : ℝ) + 1) := by
    have := Real.log_le_log (by positivity) hdm
    rw [Real.log_inv, Real.log_pow] at this
    have h2 : (((wt (plus lam)).toNat : ℕ) : ℝ) = (wt (plus lam) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hw
    rw [h2] at this; linarith
  have e2 : Real.log cc ≤ ((κ : ℝ) + 1) ^ 2 * Real.log ((plus lam 0 : ℝ) + (κ : ℝ) + 1) := by
    have := Real.log_le_log hcc hc
    rw [Real.log_pow] at this
    push_cast at this; exact this
  unfold MeanSquareWeightBound; linarith
end Formalism.HermitianLattices.LatticeEstimates
