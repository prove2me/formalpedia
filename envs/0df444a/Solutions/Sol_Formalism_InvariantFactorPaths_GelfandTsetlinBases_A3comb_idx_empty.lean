-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.idx_empty
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:38:44.42113+00:00
-- url     : https://prove2.me/submissions/5e88f60a-f7ab-423d-a04c-9199914ad501

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
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.GelfandTsetlinBases
open Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
theorem _root_.solution {n : ℕ} {μ : Fin n → ℤ} {I : ℤ → Finset (Fin n)} (hI : IsIndex μ I) (M : ℤ)
    (hM : ∀ m, |μ m| ≤ M) (c : ℤ) (hc : c ∉ Finset.Icc (-M) M) : I c = ∅ := by
  have key := hI c
  rw [Finset.mem_Icc] at hc
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    ext x
    exact x.elim0
  · have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM ⟨0, hn⟩)
    rw [← Finset.card_eq_zero, key]
    by_cases h1 : 1 ≤ c
    · rw [if_pos h1]
      unfold colHeight
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro m _
      have := hM m
      rw [abs_le] at this
      omega
    · rw [if_neg h1]
      have hall : colHeight μ c = n := by
        unfold colHeight
        rw [Finset.filter_true_of_mem, Finset.card_univ, Fintype.card_fin]
        intro m _
        have := hM m
        rw [abs_le] at this
        omega
      omega
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
