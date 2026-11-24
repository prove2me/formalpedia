-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.strip_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:44.894025+00:00
-- url     : https://prove2.me/submissions/6a49f753-9219-4049-a96e-baf0a388cbe8

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
theorem _root_.solution {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (h : HStrip ν μ b) (m : Fin n) :
    μ m ≤ ν m ∧ ν m ≤ μ m + b := by
  obtain ⟨h1, _, h3⟩ := h
  refine ⟨h1 m, ?_⟩
  have : ν m - μ m ≤ ∑ m', (ν m' - μ m') :=
    Finset.single_le_sum (f := fun m' => ν m' - μ m') (fun i _ => sub_nonneg.mpr (h1 i))
      (Finset.mem_univ m)
  rw [Finset.sum_sub_distrib, h3] at this
  linarith
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
