-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.weight_letter
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:13.688989+00:00
-- url     : https://prove2.me/submissions/d42f4018-2030-4fda-87bb-da620152a1f2

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
theorem _root_.solution {n : ℕ} (i : ℕ) (e : ℕ × Fin n →₀ ℕ) :
    Finsupp.weight (fun x : ℕ × Fin n => if x.1 = i then 1 else 0) e = ∑ a, e (i, a) := by
  refine Finsupp.induction_linear e ?_ ?_ ?_
  · simp
  · intro f g hf hg
    simp only [map_add, hf, hg, Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
  · rintro ⟨x1, x2⟩ k
    rw [Finsupp.weight_apply, Finsupp.sum_single_index]
    · by_cases hi : x1 = i
      · subst hi
        simp [Finsupp.single_apply]
      · simp [Finsupp.single_apply, hi]
    · simp
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
