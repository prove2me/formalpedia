-- Prove2me | solution 1 for Formalism.HermitianLattices.LatticeEstimates.column_other_entries
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:43.075861+00:00
-- url     : https://prove2.me/submissions/9eb5dd46-027c-40fd-a430-a1014d9c872c

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
theorem _root_.solution : Col_other := by
  intro κ lam S hS hl h0 hm
  unfold wt plus
  rw [Fin.sum_univ_succ]
  have : ∑ i : Fin κ, (lam i.succ - lam (Fin.last κ)) ≤ ∑ _i : Fin κ, (S + 1) :=
    Finset.sum_le_sum fun i _ => hm _ (Fin.succ_ne_zero i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  nlinarith
end Formalism.HermitianLattices.LatticeEstimates
