-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.root_sum_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:06:11.272069+00:00
-- url     : https://prove2.me/submissions/3e7a7f93-f7ba-4987-bf81-3f7875520232

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
theorem _root_.solution : RootSumUnitary := by
  intro m i
  rw [Pi.add_apply, Finset.sum_apply, Finset.sum_apply]
  simp only [Finset.sum_apply]
  have h1 : ∀ a b : Fin m, (if a < b then
        (2 : ℤ) • ((Pi.single a 1 : Fin m → ℤ) - Pi.single b 1) +
          (2 : ℤ) • ((Pi.single a 1 : Fin m → ℤ) + Pi.single b 1) else (0 : Fin m → ℤ)) i =
      (if a = i then (if i < b then (4 : ℤ) else 0) else 0) := by
    intro a b
    by_cases hab : a < b
    · rw [if_pos hab]
      by_cases hai : a = i
      · rw [if_pos hai, ← hai, if_pos hab]
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.single_eq_same, smul_eq_mul]
        ring
      · rw [if_neg hai]
        have h0 : (Pi.single a 1 : Fin m → ℤ) i = 0 := Pi.single_eq_of_ne (Ne.symm hai) _
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, h0, smul_eq_mul]
        ring
    · rw [if_neg hab]
      by_cases hai : a = i
      · rw [if_pos hai, ← hai, if_neg hab]; rfl
      · rw [if_neg hai]; rfl
  have h3 : ∀ a : Fin m, ((2 : ℤ) • (Pi.single a 1 : Fin m → ℤ) +
        (1 : ℤ) • ((2 : ℤ) • (Pi.single a 1 : Fin m → ℤ))) i = if a = i then 4 else 0 := by
    intro a
    by_cases hai : a = i
    · rw [if_pos hai, ← hai]
      simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      norm_num
    · rw [if_neg hai]
      have h0 : (Pi.single a 1 : Fin m → ℤ) i = 0 := Pi.single_eq_of_ne (Ne.symm hai) _
      simp only [Pi.add_apply, Pi.smul_apply, h0, smul_eq_mul]
      norm_num
  have h4 : ∀ a : Fin m, (∑ b : Fin m, if a = i then (if i < b then (4 : ℤ) else 0) else 0) =
      if a = i then ∑ b : Fin m, (if i < b then (4 : ℤ) else 0) else 0 := by
    intro a
    by_cases hai : a = i
    · simp only [if_pos hai]
    · simp only [if_neg hai, Finset.sum_const_zero]
  simp only [h1, h3, h4, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_filter, Finset.sum_const]
  have h5 : (Finset.univ.filter fun b : Fin m => i < b).card = m - 1 - i := by
    have : (Finset.univ.filter fun b : Fin m => i < b) = Finset.Ioi i := by ext; simp
    rw [this, Fin.card_Ioi]
  rw [h5]
  have := i.2
  simp only [nsmul_eq_mul]
  have h6 : ((m - 1 - (i : ℕ) : ℕ) : ℤ) = (m : ℤ) - 1 - i := by omega
  rw [h6]; ring
end Formalism.IrreducibleCountingLemmas.Z
