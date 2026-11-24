-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.weight_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:52:56.261365+00:00
-- url     : https://prove2.me/submissions/f92f0be9-9356-4dc6-a53b-403f7886d930

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ProdPowFactorizationLe
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FourMulSumLeProduct
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateThird
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_key
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_sqWeight_irred
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_divisor_square_weight_sum_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_sqSet
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_coeffs
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_sqWeight_nonneg
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_square_mass_le_one
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_biUnion_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_wtOf_mono
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
open Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
theorem _root_.solution (N : ℕ) (c₀ : Kˣ) (hq : 3 ≤ Fintype.card K) :
    wtOf (fun c : Fin N → K => sqWeight (monicOf c)) {c | c ∈ sqSet K N ∧ ∃ l : ℕ, l.Prime ∧
        l ≠ Fintype.card K ∧ ∃ x ∈ (monicOf c).rootSet L,
          primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))} ≤
      ∑ δ ∈ Finset.Icc 1 N, ((Bset K δ c₀).card : ℝ) * ((Fintype.card K : ℝ) ^ δ - 1)⁻¹ := by
  classical
  set μ : (Fin N → K) → ℝ := fun c => sqWeight (monicOf c) with hμ
  have hμ0 : ∀ c, 0 ≤ μ c := fun c => sqWeight_nonneg _
  have hsub : {c : Fin N → K | c ∈ sqSet K N ∧ ∃ l : ℕ, l.Prime ∧
        l ≠ Fintype.card K ∧ ∃ x ∈ (monicOf c).rootSet L,
          primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))} ⊆
      ⋃ δ ∈ Finset.Icc 1 N, ⋃ c' ∈ Bset K δ c₀,
        {c : Fin N → K | c ∈ sqSet K N ∧ monicOf c' ∣ monicOf c} := by
    rintro c ⟨hc, l, hl, -, x, hx, hpt⟩
    have hfx : aeval x (monicOf c) = 0 := (mem_rootSet.1 hx).2
    have hint : IsIntegral K x := ⟨monicOf c, monicOf_monic c, hfx⟩
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply ((mem_sqSet c).1 hc).2
      have : aeval (0 : L) (monicOf c) = algebraMap K L ((monicOf c).coeff 0) := by
        rw [aeval_def, eval₂_at_zero]
      rw [this, map_eq_zero] at hfx
      exact hfx
    set P := minpoly K x with hPdef
    have hPi : Irreducible P := minpoly.irreducible hint
    have hPm : P.Monic := minpoly.monic hint
    have hPd : P ∣ monicOf c := minpoly.dvd K x hfx
    have hdeg : P.natDegree ≤ N := by
      have := natDegree_le_of_dvd hPd (monicOf_monic c).ne_zero
      rwa [monicOf_natDegree] at this
    obtain ⟨l', hl', hdv⟩ := key P hPi hPm x (minpoly.aeval K x) hx0 c₀ l hl hpt hq
    have hco : monicOf (fun i : Fin P.natDegree => P.coeff i) = P := monicOf_coeffs hPm rfl
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    refine ⟨P.natDegree, Finset.mem_Icc.2 ⟨hPi.natDegree_pos, hdeg⟩,
      fun i : Fin P.natDegree => P.coeff i, ?_, hc, by rw [hco]; exact hPd⟩
    unfold Bset
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hco]
    exact ⟨hPi, l', hl', hdv⟩
  refine (wtOf_mono μ hμ0 hsub).trans ((wtOf_biUnion_le μ hμ0 _ _).trans ?_)
  refine Finset.sum_le_sum fun δ hδ => ?_
  refine (wtOf_biUnion_le μ hμ0 _ _).trans ?_
  rw [← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun c' hc' => ?_
  have hi : Irreducible (monicOf c') := (Finset.mem_filter.mp hc').2.1
  rw [wtOf_eq_filter']
  have := divisor_square_weight_sum_le square_mass_le_one K N (monicOf c') (monicOf_monic c')
    (by rw [monicOf_natDegree]; exact (Finset.mem_Icc.1 hδ).2)
    ((sqSet K N).filter (fun c => monicOf c' ∣ monicOf c))
    (fun c hc => by simpa only [Finset.mem_filter] using hc)
  rw [sqWeight_irred _ hi (monicOf_monic c'), monicOf_natDegree] at this
  exact this
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
