-- Prove2me | solution 1 for Formalism.HermitianLattices.LatticeEstimates.weight_positive_part_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:56.150796+00:00
-- url     : https://prove2.me/submissions/3a5ca89d-7a6a-4776-9963-66ef547727ea

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
theorem _root_.solution {κ : ℕ} (lam : Fin (κ + 1) → ℤ) (h : Antitone lam) : 0 ≤ wt (plus lam) := by
  unfold wt plus
  exact Finset.sum_nonneg fun i _ => by have := h (Fin.le_last i); linarith
end Formalism.HermitianLattices.LatticeEstimates
