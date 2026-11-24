-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.harm_part
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:41.24312+00:00
-- url     : https://prove2.me/submissions/d46a21c7-5448-4a24-a10a-718acaf90726

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ProdPowFactorizationLe
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FourMulSumLeProduct
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateThird
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
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
attribute [local simp] P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8



set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
theorem _root_.solution (M : ℕ) :
    ∑ δ ∈ Finset.Icc 2 (M + 1), ((δ : ℝ))⁻¹ ≤ Real.log ((M + 1 : ℕ) : ℝ) := by
  induction M with
  | zero =>
    rw [show Finset.Icc 2 (0 + 1) = (∅ : Finset ℕ) by decide]
    simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1 + 1)]
    have h1 : (0:ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have h2 : (0:ℝ) < ((m + 1 + 1 : ℕ) : ℝ) := by positivity
    have hlog := Real.log_le_sub_one_of_pos (div_pos h1 h2)
    rw [Real.log_div h1.ne' h2.ne'] at hlog
    have hab : ((m + 1 : ℕ) : ℝ) = ((m + 1 + 1 : ℕ) : ℝ) - 1 := by push_cast; ring
    have hdiv : ((m + 1 : ℕ) : ℝ) / ((m + 1 + 1 : ℕ) : ℝ) = 1 - (((m + 1 + 1 : ℕ) : ℝ))⁻¹ := by
      rw [hab, sub_div, div_self h2.ne', one_div]
    linarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
