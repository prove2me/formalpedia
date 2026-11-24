-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:51:02.766474+00:00
-- url     : https://prove2.me/submissions/4d95782b-391e-4fc3-a17d-889d4b84dd2c

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
variable {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L]
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
theorem _root_.solution (δ : ℕ) (c₀ : Kˣ) :
    δ * (Bset K δ c₀).card ≤
      ∑ l ∈ (Fintype.card K ^ δ - 1).primeFactors, l ^ padicValNat l (Fintype.card K ^ δ - 1) := by
  classical
  have hmon : ∀ c : Fin δ → K, (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c).Monic := fun c => by
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf.eq_1]
    exact Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hdegc : ∀ c : Fin δ → K, (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c).natDegree = δ := fun c => by
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf.eq_1, Polynomial.natDegree_add_eq_left_of_degree_lt,
      Polynomial.natDegree_X_pow]
    rw [Polynomial.degree_X_pow]
    exact Polynomial.degree_sum_fin_lt _
  have hcoeff : ∀ (c : Fin δ → K) (j : Fin δ), (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c).coeff j = c j := by
    intro c j
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf.eq_1, Polynomial.coeff_add, Polynomial.coeff_X_pow,
      Polynomial.finset_sum_coeff]
    simp [Polynomial.coeff_C_mul_X_pow, Fin.val_inj, j.isLt.ne]
  have hinj : Function.Injective (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf : (Fin δ → K) → K[X]) :=
    fun c c' h => funext fun j => by rw [← hcoeff c j, ← hcoeff c' j, h]
  have hgen : ∀ (k : ℕ) (a : K), 0 < k → δ * (Finset.univ.filter (fun c : Fin δ → K =>
      Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ k - C a)).card ≤ k := by
    intro k a hk
    have hF0 : (X ^ k - C a : K[X]) ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hk a
    have hprod : ∏ c ∈ Finset.univ.filter (fun c : Fin δ → K =>
        Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧ Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ k - C a),
        Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ k - C a := by
      apply Finset.prod_dvd_of_coprime
      · intro c hc c' hc' hne
        have hi := (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2.1
        have hi' := (Finset.mem_filter.mp (Finset.mem_coe.mp hc')).2.1
        show IsCoprime (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c')
        rw [hi.coprime_iff_not_dvd]
        intro hdvd
        apply hne
        apply hinj
        exact Polynomial.eq_of_monic_of_associated (hmon c) (hmon c') (hi.associated_of_dvd hi' hdvd)
      · intro c hc
        exact (Finset.mem_filter.mp hc).2.2
    have hdeg := Polynomial.natDegree_le_of_dvd hprod hF0
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun c _ => hmon c),
      Polynomial.natDegree_X_pow_sub_C] at hdeg
    simp only [hdegc, Finset.sum_const, smul_eq_mul] at hdeg
    rw [mul_comm]
    exact hdeg
  set m := Fintype.card K ^ δ - 1 with hmdef
  have hsub : Bset K δ c₀ ⊆ m.primeFactors.biUnion (fun l' => Finset.univ.filter
      (fun c : Fin δ → K => Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧
        Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ (l' ^ padicValNat l' m) - C ((c₀ : K) ^ (l' ^ padicValNat l' m)))) := by
    intro c hc
    simp only [Bset, Finset.mem_filter, Finset.mem_univ, true_and] at hc
    obtain ⟨hirr, l', hl', hdvd⟩ := hc
    exact Finset.mem_biUnion.mpr ⟨l', hl', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hirr, hdvd⟩⟩
  calc δ * (Bset K δ c₀).card
      ≤ δ * (m.primeFactors.biUnion (fun l' => Finset.univ.filter
      (fun c : Fin δ → K => Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧
        Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ (l' ^ padicValNat l' m) - C ((c₀ : K) ^ (l' ^ padicValNat l' m))))).card :=
        Nat.mul_le_mul le_rfl (Finset.card_le_card hsub)
    _ ≤ δ * ∑ l' ∈ m.primeFactors, (Finset.univ.filter
      (fun c : Fin δ → K => Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧
        Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ (l' ^ padicValNat l' m) - C ((c₀ : K) ^ (l' ^ padicValNat l' m)))).card :=
        Nat.mul_le_mul le_rfl Finset.card_biUnion_le
    _ = ∑ l' ∈ m.primeFactors, δ * (Finset.univ.filter
      (fun c : Fin δ → K => Irreducible (Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c) ∧
        Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.monicOf c ∣ X ^ (l' ^ padicValNat l' m) - C ((c₀ : K) ^ (l' ^ padicValNat l' m)))).card := by
        rw [Finset.mul_sum]
    _ ≤ ∑ l' ∈ m.primeFactors, l' ^ padicValNat l' m := by
        apply Finset.sum_le_sum
        intro l' hl'
        exact hgen _ _ (pow_pos (Nat.prime_of_mem_primeFactors hl').pos _)
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
