-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting.expSet_subset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:54:14.318094+00:00
-- url     : https://prove2.me/submissions/2bdec810-22f3-4be2-8363-ce81ffda9beb

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_CorA3primeB
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ValuationProductsComponents
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_ExistsSuppOfEvalNe
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_NormIndexCountBound
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_UnitAndFieldPowerLemmas
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_ExponentSetCounting_shift_inj

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
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
variable {n : ℕ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
theorem _root_.solution (n i N : ℕ) (B : ℕ → ℕ) :
    expSet n i N B ⊆ Finsupp.mapDomain (fun x : ℕ × Fin n => (i + x.1, x.2)) ''
      {e : ℕ × Fin n →₀ ℕ | ∀ j, ∑ a, e (j, a) = if j < N - i then B (i + j) else 0} := by
  intro β hβ
  have hβ' : ∀ j, ∑ a, β (j, a) = if i ≤ j ∧ j < N then B j else 0 := hβ
  have hsupp : ↑β.support ⊆ Set.range (fun x : ℕ × Fin n => (i + x.1, x.2)) := by
    intro p hp
    obtain ⟨j, a⟩ := p
    have hpa : β (j, a) ≠ 0 := Finsupp.mem_support_iff.mp hp
    have hij : i ≤ j := by
      by_contra hlt
      have h0 := hβ' j
      rw [if_neg (fun h => hlt h.1)] at h0
      exact hpa ((Finset.sum_eq_zero_iff.mp h0) a (Finset.mem_univ a))
    exact ⟨(j - i, a), Prod.ext (show i + (j - i) = j by omega) rfl⟩
  refine ⟨Finsupp.comapDomain _ β (fun _ _ _ _ h => shift_inj n i h), ?_, ?_⟩
  · simp only [Set.mem_setOf_eq]
    intro j
    show ∑ a, β (i + j, a) = _
    rw [hβ' (i + j)]
    by_cases h : j < N - i
    · rw [if_pos ⟨by omega, by omega⟩, if_pos h]
    · rw [if_neg (by omega), if_neg h]
  · apply Finsupp.mapDomain_comapDomain
    · exact shift_inj n i
    · exact hsupp
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.ExponentSetCounting
