-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.prod_Ioc_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:48:00.69284+00:00
-- url     : https://prove2.me/submissions/94146b64-7460-46a1-94e6-302cdfca81b5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof

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
open SignTwistStarLemmas
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
variable {k : Type} [Field k] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
theorem _root_.solution {M : Type*} [CommMonoid M] (lo hi : ℤ) (f : ℤ → M) :
    ∏ c ∈ Finset.Ioc lo hi, f c = ∏ t : Fin (hi - lo).toNat, f (lo + 1 + (t.val : ℤ)) := by
  symm
  refine Finset.prod_bij (fun t _ => lo + 1 + (t.val : ℤ)) ?_ ?_ ?_ ?_
  · intro t _
    have := t.2
    rw [Finset.mem_Ioc]; omega
  · intro t _ t' _ h
    apply Fin.ext; omega
  · intro c hc
    rw [Finset.mem_Ioc] at hc
    exact ⟨⟨(c - lo - 1).toNat, by omega⟩, mem_univ _, by simp only []; omega⟩
  · intro t _; rfl
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
