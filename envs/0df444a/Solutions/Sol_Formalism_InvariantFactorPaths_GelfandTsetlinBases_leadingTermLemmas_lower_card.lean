-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.lower_card
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:48:31.879314+00:00
-- url     : https://prove2.me/submissions/38a23ae4-f5ea-4b97-a98a-0aee63457c73

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
variable {n C : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
theorem _root_.solution (S : Finset (Fin C)) (hS : ∀ c ∈ S, ∀ c' ≤ c, c' ∈ S) (c : Fin C) :
    c ∈ S ↔ c.val < S.card := by
  constructor
  · intro hc
    have : Finset.Iic c ⊆ S := fun c' hc' => hS c hc c' (Finset.mem_Iic.1 hc')
    have := Finset.card_le_card this
    rw [Fin.card_Iic] at this
    omega
  · intro hlt
    by_contra hc
    have : S ⊆ Finset.Iio c := by
      intro s hs
      rw [Finset.mem_Iio]
      by_contra hcs
      exact hc (hS s hs c (not_lt.1 hcs))
    have := Finset.card_le_card this
    rw [Fin.card_Iio] at this
    omega
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
