-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.local_estimate_third
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:11:26.275535+00:00
-- url     : https://prove2.me/submissions/4f50b94a-c6e9-44da-9646-cf1d3d53d121

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ProdPowFactorizationLe
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FourMulSumLeProduct
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateThird
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_arith
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_count
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_weight_le
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_prime_power_order_count
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_prime_power_order_share
import Theorems.Thm_P2M_Formalism_GaloisIrreducibility_BorderedIndexCases_zero_ne_succ__49ef2f236cb8
import Theorems.Thm_P2M_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_eq_filter__b757eed49bc8
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
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : LocalEstimateIII := by
  classical
  intro K L _ _ _ _ _ N q₁ d c₀ hN hq1 hd hne h12 hd2 hmax h16 hq1d hdd
  have hq2 : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hq17 : 17 ≤ Fintype.card K := by
    have := Nat.le_of_dvd (by omega) h16
    omega
  have hw := E4.weight_le (L := L) N c₀ (by omega)
  rw [wtOf_eq_filter'] at hw
  have c1 : ((Fintype.card K - 1 : ℕ) : ℝ) = (Fintype.card K : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have h1 : (((E4.Bset K 1 c₀).card : ℕ) : ℝ) * ((Fintype.card K : ℝ) - 1)⁻¹ ≤
      1 / (4 * (min q₁ d : ℕ)) := by
    have hc := E4.count 1 c₀
    rw [one_mul, pow_one] at hc
    have hs := prime_power_order_share (Fintype.card K) q₁ d hq2 hq1 hd hne h12 hd2 hmax h16
      hq1d hdd
    refine le_trans ?_ hs
    rw [c1, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hc
    · apply inv_nonneg.2
      have : (17 : ℝ) ≤ (Fintype.card K : ℝ) := by exact_mod_cast hq17
      linarith
  have h2 : ∀ δ, 2 ≤ δ → δ * (E4.Bset K δ c₀).card ≤
      δ * (Fintype.card K - 1) + (Fintype.card K ^ δ - 1) / (Fintype.card K - 1) := fun δ hδ =>
    (E4.count δ c₀).trans (prime_power_order_count (Fintype.card K) δ hq2
      (dvd_trans (by norm_num) h16) (by omega))
  have ha := E4.arith (Fintype.card K) N hN hq2 (fun δ => (E4.Bset K δ c₀).card) _ h1 h2
  exact hw.trans ha
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
