-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.arith
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:33.512061+00:00
-- url     : https://prove2.me/submissions/250d894e-28fc-42ca-b3fd-a0810dbb198f

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ProdPowFactorizationLe
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FourMulSumLeProduct
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateThird
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_geom_part
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_harm_part
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_term_le
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
theorem _root_.solution (q N : ℕ) (hN : 1 ≤ N) (hq : 2 ≤ q) (b : ℕ → ℕ) (m : ℝ)
    (h1 : (b 1 : ℝ) * ((q : ℝ) - 1)⁻¹ ≤ m)
    (h2 : ∀ δ, 2 ≤ δ → δ * b δ ≤ δ * (q - 1) + (q ^ δ - 1) / (q - 1)) :
    ∑ δ ∈ Finset.Icc 1 N, (b δ : ℝ) * ((q : ℝ) ^ δ - 1)⁻¹ ≤
      m + (1 + Real.log N) / ((q : ℝ) - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hQ : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 1 < q)
  have hQ1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (by omega : 1 ≤ M + 1)]
  have hI : Finset.Ioc 1 (M + 1) = Finset.Icc 2 (M + 1) := by
    ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
  rw [hI, pow_one]
  have h3 : ∑ δ ∈ Finset.Icc 2 (M + 1), (b δ : ℝ) * ((q : ℝ) ^ δ - 1)⁻¹ ≤
      ∑ δ ∈ Finset.Icc 2 (M + 1), (((q : ℝ) ^ (δ - 1))⁻¹ + ((δ : ℝ))⁻¹ * ((q : ℝ) - 1)⁻¹) :=
    Finset.sum_le_sum fun δ hδ =>
      term_le q δ (b δ) hq (Finset.mem_Icc.1 hδ).1 (h2 δ (Finset.mem_Icc.1 hδ).1)
  rw [Finset.sum_add_distrib, ← Finset.sum_mul] at h3
  have h4 := geom_part (q : ℝ) hQ M
  have h5 := harm_part M
  have h6 : (1 - ((q : ℝ) ^ M)⁻¹) / ((q : ℝ) - 1) ≤ 1 / ((q : ℝ) - 1) := by
    apply div_le_div_of_nonneg_right _ hQ1.le
    have : 0 ≤ ((q : ℝ) ^ M)⁻¹ := by positivity
    linarith
  have h7 : (∑ δ ∈ Finset.Icc 2 (M + 1), ((δ : ℝ))⁻¹) * ((q : ℝ) - 1)⁻¹ ≤
      Real.log ((M + 1 : ℕ) : ℝ) * ((q : ℝ) - 1)⁻¹ :=
    mul_le_mul_of_nonneg_right h5 (inv_nonneg.2 hQ1.le)
  have h8 : (1 + Real.log ((M + 1 : ℕ) : ℝ)) / ((q : ℝ) - 1) =
      1 / ((q : ℝ) - 1) + Real.log ((M + 1 : ℕ) : ℝ) * ((q : ℝ) - 1)⁻¹ := by
    rw [add_div, div_eq_mul_inv (Real.log _)]
  rw [h8]
  linarith
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
