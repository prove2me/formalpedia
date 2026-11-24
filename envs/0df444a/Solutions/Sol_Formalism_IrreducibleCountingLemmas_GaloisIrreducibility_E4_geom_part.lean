-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.geom_part
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:08:41.029293+00:00
-- url     : https://prove2.me/submissions/3de3e717-20cb-4244-b6c5-eb9ca31bb4b4

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
theorem _root_.solution (Q : ℝ) (hQ : 1 < Q) (M : ℕ) :
    ∑ δ ∈ Finset.Icc 2 (M + 1), (Q ^ (δ - 1))⁻¹ ≤ (1 - (Q ^ M)⁻¹) / (Q - 1) := by
  have hQ1 : Q - 1 ≠ 0 := (sub_pos.mpr hQ).ne'
  have hQ0 : Q ≠ 0 := by positivity
  suffices h : ∑ δ ∈ Finset.Icc 2 (M + 1), (Q ^ (δ - 1))⁻¹ = (1 - (Q ^ M)⁻¹) / (Q - 1) from h.le
  induction M with
  | zero =>
    rw [show Finset.Icc 2 (0 + 1) = (∅ : Finset ℕ) by decide]
    simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1 + 1), ih, Nat.add_sub_cancel]
    field_simp
    ring
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
