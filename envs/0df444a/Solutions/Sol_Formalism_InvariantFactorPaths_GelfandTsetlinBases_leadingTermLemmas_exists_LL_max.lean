-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas.exists_LL_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:48:29.554466+00:00
-- url     : https://prove2.me/submissions/87ff5f15-ab64-4aff-bf49-93d76765781b

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_StatementA
import Definitions.Def_Lemmata_GeneralBFactRightFurther_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LinearIndependentOfLead
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_LL_trans
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_leadingTermLemmas_LL_total

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
variable {σ τ : Type*} [LinearOrder τ] (κ : σ → τ)
variable {κ}
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
theorem _root_.solution (hκ : Function.Injective κ) {ι : Type*} (d : ι → σ →₀ ℕ) (hd : Function.Injective d)
    (s : Finset ι) (hs : s.Nonempty) : ∃ i ∈ s, ∀ j ∈ s, j ≠ i → LL κ (d j) (d i) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    exact ⟨a, Finset.mem_singleton_self a, fun j hj hne => absurd (Finset.mem_singleton.1 hj) hne⟩
  | cons a s ha hs ih =>
    obtain ⟨i, his, hi⟩ := ih
    have hai : a ≠ i := fun h => ha (h ▸ his)
    rcases LL_total (κ := κ) (fun h => hai (hd h) : d a ≠ d i) with h1 | h1
    · refine ⟨i, Finset.mem_cons.2 (Or.inr his), fun j hj hne => ?_⟩
      rcases Finset.mem_cons.1 hj with rfl | hj
      · exact h1
      · exact hi j hj hne
    · refine ⟨a, Finset.mem_cons_self a s, fun j hj hne => ?_⟩
      rcases Finset.mem_cons.1 hj with rfl | hj
      · exact absurd rfl hne
      · by_cases hji : j = i
        · rw [hji]; exact h1
        · exact LL_trans hκ (hi j hj hji) h1
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.leadingTermLemmas
