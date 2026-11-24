-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.minorF_univ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:47:59.782+00:00
-- url     : https://prove2.me/submissions/43fea203-8abb-4744-8c7c-0d23439f8393

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_minorF_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_minorF_ne


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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
variable {R : Type} [CommRing R] {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
theorem _root_.solution (m : Matrix (Fin n) (Fin n) R) (J : Finset (Fin n)) :
    minorF m univ J = if J = univ then m.det else 0 := by
  split_ifs with h
  · subst h
    have hc : (univ : Finset (Fin n)).card = n := by simp
    rw [minorF_eq m hc hc]
    have : (id : Fin n → Fin n) = (univ : Finset (Fin n)).orderEmbOfFin hc := by
      apply Finset.orderEmbOfFin_unique
      · intro x; simp
      · exact strictMono_id
    rw [← this, Matrix.submatrix_id_id]
  · apply minorF_ne
    intro hc
    exact h ((Finset.card_eq_iff_eq_univ J).1 (by rw [hc, Finset.card_univ]))
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
