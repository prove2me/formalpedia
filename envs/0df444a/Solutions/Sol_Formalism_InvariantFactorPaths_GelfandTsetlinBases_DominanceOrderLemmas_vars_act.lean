-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas.vars_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:54:39.4279+00:00
-- url     : https://prove2.me/submissions/cd69cd8f-e97c-4175-846d-be70f0feb9ab

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LemmaA2indepOf
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GenSpace
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_GoodWOfWeight
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_DominanceOrderLemmas_vars_actX

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas
theorem _root_.solution {L : Type*} [CommRing L] [Nontrivial L] {n N : ℕ} (isVec : ℕ → Bool)
    (g gi : Matrix (Fin n) (Fin n) L) {P : MvPolynomial (ℕ × Fin n) L} (hv : ∀ x ∈ P.vars, x.1 < N) :
    ∀ y ∈ (actAll isVec g gi P).vars, y.1 < N := by
  intro y hy
  have heq : actAll isVec g gi P = bind₁ (fun x => actAll isVec g gi (X x)) P := by
    simp only [actAll, bind₁, aeval_X]
  rw [heq] at hy
  obtain ⟨x, hx, hyx⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_bind₁ _ _ hy)
  rw [vars_actX isVec g gi x y hyx]
  exact hv x hx
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.DominanceOrderLemmas
