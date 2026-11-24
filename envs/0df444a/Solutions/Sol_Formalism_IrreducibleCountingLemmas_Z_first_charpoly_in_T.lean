-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.first_charpoly_in_T
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:47.197606+00:00
-- url     : https://prove2.me/submissions/f783932e-7350-4467-adc5-0378da53c620

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_natAdd
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_succ_zero
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_succ
attribute [local simp] Formalism.GaloisIrreducibility.BorderedIndexCases.bord_zero_zero
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_natAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_natAdd
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Polynomial Filter Topology
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : CharpolyOverSubalgebra := by
  intro O _ _ X' _ T n M h
  have hdeg : ∀ x, (M x).charpoly.natDegree = n := fun x => by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hco : ∀ (x : X') (j : ℕ), j ≤ n →
      (M x).charpoly.coeff j = (Matrix.charpolyRev (M x)).coeff (n - j) := by
    intro x j hj
    rw [← Matrix.reverse_charpoly, coeff_reverse, hdeg, revAt_le (Nat.sub_le n j),
      Nat.sub_sub_self hj]
  have hmem : ∀ j : ℕ, (fun x => (M x).charpoly.coeff j) ∈ T := by
    intro j
    by_cases hj : j ≤ n
    · have : (fun x => (M x).charpoly.coeff j) =
          fun x => (Matrix.charpolyRev (M x)).coeff (n - j) := funext fun x => hco x j hj
      rw [this]; exact h _
    · have : (fun x => (M x).charpoly.coeff j) = 0 := funext fun x =>
        coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)
      rw [this]; exact T.zero_mem
  let F : T[X] := ∑ j ∈ Finset.range (n + 1), C (⟨_, hmem j⟩ : T) * X ^ j
  have hFc : ∀ j, F.coeff j = if j ≤ n then (⟨_, hmem j⟩ : T) else 0 := by
    intro j
    simp only [F, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp
  refine ⟨F, ?_, fun x => ?_⟩
  · apply monic_of_natDegree_le_of_coeff_eq_one n
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro N hN
      rw [hFc, if_neg (by omega)]
    · rw [hFc, if_pos le_rfl]
      apply Subtype.ext
      funext x
      have := (Matrix.charpoly_monic (M x)).coeff_natDegree
      rw [hdeg] at this
      exact this
  · ext j
    rw [coeff_map, hFc]
    by_cases hj : j ≤ n
    · rw [if_pos hj]; rfl
    · rw [if_neg hj, map_zero]
      exact (coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega)).symm
end Formalism.IrreducibleCountingLemmas.Z
