-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.sum_emb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:47:50.517038+00:00
-- url     : https://prove2.me/submissions/47e1a0d4-36c2-47b7-a512-b15142593b30

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
theorem _root_.solution {M : Type*} [AddCommMonoid M] (J : Finset (Fin n)) {k : ℕ} (h : J.card = k) (F : Fin n → M) :
    ∑ b ∈ J, F b = ∑ i : Fin k, F (J.orderEmbOfFin h i) := by
  conv_lhs => rw [← Finset.map_orderEmbOfFin_univ J h]
  rw [Finset.sum_map]
  rfl
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
