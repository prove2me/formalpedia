-- Prove2me | solution 1 for Formalism.HermitianLattices.LatticeEstimates.L1LeSqrtCardOfL2_statement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:42.219442+00:00
-- url     : https://prove2.me/submissions/fe7e6535-015c-4234-b26a-8dd3799541bb

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
theorem _root_.solution : L1LeSqrtCardOfL2 := by
  intro ι _ c h
  apply Real.le_sqrt_of_sq_le
  have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset ι)) (f := fun e => ‖c e‖)
  simp only [Finset.card_univ] at this
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]
end Formalism.HermitianLattices.LatticeEstimates
