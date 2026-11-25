-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.weight_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:06:34.28718+00:00
-- url     : https://prove2.me/submissions/e935fff7-9f38-49da-9013-e6560e97deea

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
theorem _root_.solution {n : ℕ} (isVec : ℕ → Bool) (e : ℕ × Fin n →₀ ℕ) (m : Fin n) :
    Finsupp.weight (torusW isVec) e m =
      Finsupp.weight
        (fun x : ℕ × Fin n => if x.2 = m then (if isVec x.1 then (1 : ℤ) else -1) else 0) e := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x.2 = m
  · subst hx
    by_cases hv : isVec x.1 <;> simp [torusW, hv]
  · have hx' : m ≠ x.2 := fun h => hx h.symm
    by_cases hv : isVec x.1 <;> simp [torusW, hv, hx, hx', Pi.single_apply]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
