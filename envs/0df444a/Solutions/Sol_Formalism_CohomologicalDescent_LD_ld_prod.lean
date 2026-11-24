-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LD.ld_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:54:22.924792+00:00
-- url     : https://prove2.me/submissions/a85fc03c-3510-40b5-ab93-12f2619c1ce7

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_minor
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility
namespace Formalism.CohomologicalDescent.LD
theorem _root_.solution {K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ 2) (I : ∀ k, Fin (sz k) → Fin 2)
    (S : Finset (Fin K)) :
    ∃ (ε : ℤ) (α β : ℕ), ∏ k ∈ S, initMinor ℤ (I k) (hsz k) =
        C ε * (X (0, 0) ^ α * X (1, 0) ^ β * ldDet ^ (S.filter fun k => 1 < sz k).card) ∧
      α + β + (S.filter fun k => 1 < sz k).card = (S.filter fun k => 0 < sz k).card := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, 0, 0, by simp, by simp⟩
  | insert k S hk ih =>
    obtain ⟨ε, α, β, hprod, hcard⟩ := ih
    have hk1 : k ∉ S.filter fun k => 1 < sz k := fun h => hk (Finset.mem_filter.mp h).1
    have hk0 : k ∉ S.filter fun k => 0 < sz k := fun h => hk (Finset.mem_filter.mp h).1
    rw [Finset.prod_insert hk, hprod, Finset.filter_insert, Finset.filter_insert]
    rcases ld_minor (sz k) (I k) (hsz k) with ⟨h0, hm⟩ | ⟨h1, a, hm⟩ | ⟨h2, ε', hm⟩
    · rw [hm, if_neg (by omega), if_neg (by omega)]
      exact ⟨ε, α, β, by ring, hcard⟩
    · rw [hm, if_neg (by omega), if_pos (by omega), Finset.card_insert_of_notMem hk0]
      have ha : a = 0 ∨ a = 1 := by omega
      rcases ha with rfl | rfl
      · exact ⟨ε, α + 1, β, by ring, by omega⟩
      · exact ⟨ε, α, β + 1, by ring, by omega⟩
    · rw [hm, if_pos (by omega), if_pos (by omega), Finset.card_insert_of_notMem hk0,
        Finset.card_insert_of_notMem hk1]
      exact ⟨ε' * ε, α, β, by rw [C_mul]; ring, by omega⟩
end Formalism.CohomologicalDescent.LD
