-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.inert_parameter_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:17:19.889811+00:00
-- url     : https://prove2.me/submissions/de76d0c0-6275-474b-a586-8d4fb6c70206

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_FactorOverLocalSubalgebraMonic
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZCircleCharExtends
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FactorOverLocalSubalgebra
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CharpolyFactorAnnihilator
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZGoodCuspidal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CardLtAddCardGtAddCardEq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_hull_bound_signed
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
theorem _root_.solution : InertParameterBound := by
  intro r m q x α hr hq hα hx β hβ
  have hb := hull_bound_signed r m x hr hx
  have hr0 : (0 : ℝ) ≤ ((r : ℝ) - 1) / 2 := by
    have : ((r : ℝ) - 1) / 2 = m := by rw [hr]; push_cast; ring
    rw [this]; exact Nat.cast_nonneg _
  simp only [Multiset.mem_add, Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and,
    Multiset.mem_singleton] at hβ
  rcases hβ with (⟨i, rfl⟩ | ⟨i, rfl⟩) | rfl
  · rw [hα]
    exact Real.rpow_le_rpow_of_exponent_le hq.le (abs_le.1 (hb i)).2
  · rw [norm_inv, hα, ← Real.rpow_neg (by linarith)]
    exact Real.rpow_le_rpow_of_exponent_le hq.le (by have := (abs_le.1 (hb i)).1; linarith)
  · rw [norm_one]
    exact Real.one_le_rpow hq.le hr0
end Formalism.IrreducibleCountingLemmas.Z
