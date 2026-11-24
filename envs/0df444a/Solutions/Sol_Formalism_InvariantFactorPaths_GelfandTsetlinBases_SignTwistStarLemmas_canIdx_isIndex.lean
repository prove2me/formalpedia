-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas.canIdx_isIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:47:55.573517+00:00
-- url     : https://prove2.me/submissions/88d13388-315d-4add-acd8-a52822e32ed5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ActFormContract
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_JacobiMinorProof
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_Paths_colHeight_le


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
theorem _root_.solution (μ : Fin n → ℤ) : IsIndex μ (canIdx μ) := by
  intro c
  have hle := Paths.colHeight_le μ c
  have h1 : (univ.filter fun m : Fin n => m.val < colHeight μ c).card = colHeight μ c := by
    rw [Fin.card_filter_val_lt]; omega
  unfold canIdx
  split_ifs with hc
  · exact h1
  · have h2 : (univ.filter fun m : Fin n => colHeight μ c ≤ m.val) =
        (univ.filter fun m : Fin n => m.val < colHeight μ c)ᶜ := by
      ext m; simp
    rw [h2, Finset.card_compl, h1, Fintype.card_fin]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.SignTwistStarLemmas
