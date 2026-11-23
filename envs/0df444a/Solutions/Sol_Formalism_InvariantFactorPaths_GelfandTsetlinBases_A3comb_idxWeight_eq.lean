-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.idxWeight_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:25.370628+00:00
-- url     : https://prove2.me/submissions/4571d801-c2e1-41d8-bb32-1b700f9e2854

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases
namespace A3comb
private theorem ncard_eq_filter_lemma {n : ℕ} (I : ℤ → Finset (Fin n)) (S : Finset ℤ)
    (hS : ∀ c, c ∉ S → I c = ∅) (m : Fin n) (p : ℤ → Prop) [DecidablePred p] :
    ({c : ℤ | p c ∧ m ∈ I c}.ncard : ℤ) = ((S.filter fun c => p c ∧ m ∈ I c).card : ℤ) := by
  congr 1
  rw [← Set.ncard_coe_finset]
  congr 1
  ext c
  simp only [Set.mem_setOf_eq, Finset.mem_coe, Finset.mem_filter]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1, h2⟩
    by_contra hcS
    rw [hS c hcS] at h2
    simp at h2
  · rintro ⟨_, h1, h2⟩
    exact ⟨h1, h2⟩
end A3comb
namespace A3comb
end A3comb
namespace A3comb
end A3comb
namespace A3comb
end A3comb
end Formalism.InvariantFactorPaths.GelfandTsetlinBases
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
theorem _root_.solution {n : ℕ} (I : ℤ → Finset (Fin n)) (S : Finset ℤ) (hS : ∀ c, c ∉ S → I c = ∅)
    (m : Fin n) :
    idxWeight I m = ∑ c ∈ S, (if m ∈ I c then (if 1 ≤ c then (1 : ℤ) else -1) else 0) := by
  unfold idxWeight
  rw [ncard_eq_filter_lemma I S hS m (fun c => 1 ≤ c), ncard_eq_filter_lemma I S hS m (fun c => c ≤ 0),
    Finset.card_filter, Finset.card_filter]
  push_cast
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hm : m ∈ I c
  · by_cases hc : 1 ≤ c
    · have h0 : ¬ c ≤ 0 := by omega
      simp [hm, hc, h0]
    · have h0 : c ≤ 0 := by omega
      simp [hm, hc, h0]
  · simp [hm]
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
