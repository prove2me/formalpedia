-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb.monSet_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:47:20.071339+00:00
-- url     : https://prove2.me/submissions/fa8edf0d-2382-4eab-b689-c2eae45e417c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_IndexWeightsDominance
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_LeIffLtColHeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_PathProductHighestWeight
import Definitions.Def_Formalism_ThetaLogCoordinates_JacobiPathWeights_JacobiMinorProofs_IndexWeightsDominance
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_mkMon_apply
import Theorems.Thm_Formalism_InvariantFactorPaths_GelfandTsetlinBases_A3comb_mkMon_apply_ge

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
theorem _root_.solution (n N : ℕ) (B : ℕ → ℕ) :
    {e : ℕ × Fin n →₀ ℕ | ∀ i, ∑ a, e (i, a) = if i < N then B i else 0} =
      ↑((Fintype.piFinset fun i : Fin N => (univ : Finset (Fin n)).finsuppAntidiag (B i)).image
        mkMon) := by
  ext e
  simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
    Fintype.mem_piFinset, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  constructor
  · intro he
    refine ⟨fun i => Finsupp.equivFunOnFinite.symm fun a => e (i.val, a), fun i => ?_, ?_⟩
    · simpa using he i.val
    · ext ⟨j, a⟩
      by_cases hj : j < N
      · exact (mkMon_apply _ ⟨j, hj⟩ a).trans (by simp)
      · rw [mkMon_apply_ge _ _ hj]
        have := he j
        rw [if_neg hj, Finset.sum_eq_zero_iff] at this
        exact (this a (Finset.mem_univ a)).symm
  · rintro ⟨d, hd, rfl⟩ i
    by_cases hi : i < N
    · rw [if_pos hi]
      exact (Finset.sum_congr rfl fun a _ => mkMon_apply d ⟨i, hi⟩ a).trans (hd ⟨i, hi⟩)
    · rw [if_neg hi]
      exact Finset.sum_eq_zero fun a _ => mkMon_apply_ge d i hi a
end Formalism.InvariantFactorPaths.GelfandTsetlinBases.A3comb
