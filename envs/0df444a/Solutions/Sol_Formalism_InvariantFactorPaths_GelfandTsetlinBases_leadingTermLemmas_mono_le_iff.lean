-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.mono_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:55:29.856962+00:00
-- url     : https://prove2.me/submissions/0451becc-66bf-4827-a0da-e616b233e9ef

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_lower_card

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
theorem _root_.solution (f : Fin C → ℕ) (hf : Monotone f) (v : ℕ) (c : Fin C) :
    f c ≤ v ↔ c.val < ∑ w ∈ Finset.range (v + 1), (univ.filter fun c => f c = w).card := by
  classical
  have h1 : (univ.filter fun c => f c ≤ v).card =
      ∑ w ∈ Finset.range (v + 1), (univ.filter fun c => f c = w).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.range (v + 1))]
    · refine Finset.sum_congr rfl fun w hw => ?_
      congr 1
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by have := Finset.mem_range.1 hw; omega, h⟩
    · intro c hc
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hc
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
  rw [← h1, ← lower_card]
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · intro c hc c' hcc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact (hf hcc).trans hc
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
