-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4.key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T09:50:46.010556+00:00
-- url     : https://prove2.me/submissions/018f65f6-6fe8-47da-8714-d0c7448086a4

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ProdPowFactorizationLe
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FourMulSumLeProduct
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateThird
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_E4_exists_prime_pow_eq
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
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
theorem _root_.solution (P : K[X]) (hP : Irreducible P) (hm : P.Monic) (x : L) (hx : aeval x P = 0)
    (hx0 : x ≠ 0) (c₀ : Kˣ) (l : ℕ) (hl : l.Prime)
    (h : primeToPart l x = primeToPart l (algebraMap K L (c₀ : K))) (hq : 3 ≤ Fintype.card K) :
    ∃ l' ∈ (Fintype.card K ^ P.natDegree - 1).primeFactors,
      P ∣ X ^ (l' ^ padicValNat l' (Fintype.card K ^ P.natDegree - 1)) -
        C ((c₀ : K) ^ (l' ^ padicValNat l' (Fintype.card K ^ P.natDegree - 1))) := by
  classical
  set q := Fintype.card K with hqdef
  set d := P.natDegree with hd
  set n := q ^ d - 1 with hn
  have hint : IsIntegral K x := ⟨P, hm, by rwa [Polynomial.aeval_def] at hx⟩
  have hmin : P = minpoly K x := minpoly.eq_of_irreducible_of_monic hP hx hm
  have hd1 : 1 ≤ d := by
    rw [hd]
    exact Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hP)
  have hqd : 3 ≤ q ^ d := le_trans hq (Nat.le_self_pow (by omega) q)
  have hn2 : 2 ≤ n := by omega
  have hxn : x ^ n = 1 := by
    haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
      IntermediateField.adjoin.finiteDimensional hint
    haveI : Finite (IntermediateField.adjoin K {x}) := Module.finite_of_finite K
    letI : Fintype (IntermediateField.adjoin K {x}) := Fintype.ofFinite _
    have hcard : Fintype.card (IntermediateField.adjoin K {x}) = q ^ d := by
      rw [Module.card_eq_pow_finrank (K := K), IntermediateField.adjoin.finrank hint, ← hmin]
    have hxE : (⟨x, IntermediateField.mem_adjoin_simple_self K x⟩ : IntermediateField.adjoin K {x}) ≠ 0 := by
      intro h0
      exact hx0 (congrArg Subtype.val h0)
    have h1 := FiniteField.pow_card_sub_one_eq_one _ hxE
    rw [hcard] at h1
    have h2 := congrArg (fun e : IntermediateField.adjoin K {x} => (e : L)) h1
    simpa using h2
  have hc0 : (c₀ : K) ≠ 0 := c₀.ne_zero
  have hcK : (c₀ : K) ^ n = 1 := by
    have h1 := FiniteField.pow_card_pow d (c₀ : K)
    have h2 : (c₀ : K) ^ n * (c₀ : K) = (c₀ : K) := by
      rw [← pow_succ, hn, Nat.sub_add_cancel (by omega : 1 ≤ q ^ d)]
      exact h1
    exact mul_right_cancel₀ hc0 (h2.trans (one_mul _).symm)
  have hcL : algebraMap K L (c₀ : K) ≠ 0 := (_root_.map_ne_zero _).mpr hc0
  have hcn : algebraMap K L (c₀ : K) ^ n = 1 := by rw [← map_pow, hcK, map_one]
  have aux : ∀ z : L, z ≠ 0 → z ^ n = 1 →
      ∃ E : ℕ, (z / Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart l z) ^ (l ^ E) = 1 := by
    intro z hz0 hzn
    have ho : 0 < orderOf z :=
      orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, by omega, hzn⟩)
    have key2 : ∀ a b : ℕ, a ≡ b [MOD orderOf z] → z ^ a = z ^ b := fun a b hab => by
      rw [← pow_mod_orderOf z a, ← pow_mod_orderOf z b]
      exact congrArg (fun k => z ^ k) hab
    refine ⟨(orderOf z).factorization l, ?_⟩
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart.eq_1]
    have hcop : (l ^ (orderOf z).factorization l).Coprime
        (orderOf z / l ^ (orderOf z).factorization l) :=
      (Nat.coprime_ordCompl hl ho.ne').pow_left _
    have hmod := (Nat.ModEq.pow_totient hcop).mul_right' (l ^ (orderOf z).factorization l)
    rw [one_mul, Nat.div_mul_cancel (Nat.ordProj_dvd (orderOf z) l)] at hmod
    rw [div_pow, ← pow_mul z, key2 _ _ hmod, div_self (pow_ne_zero _ hz0)]
  obtain ⟨E1, hE1⟩ := aux x hx0 hxn
  obtain ⟨E2, hE2⟩ := aux _ hcL hcn
  rw [h] at hE1
  have hp0 : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart l (algebraMap K L (c₀ : K)) ≠ 0 := by
    rw [Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.primeToPart.eq_1]
    exact pow_ne_zero _ hcL
  have hyE : (x / algebraMap K L (c₀ : K)) ^ (l ^ (E1 + E2)) = 1 := by
    rw [← div_div_div_cancel_right₀ hp0 x (algebraMap K L (c₀ : K)), div_pow, pow_add,
      pow_mul (x / _), hE1, one_pow, mul_comm (l ^ E1), pow_mul, hE2, one_pow, div_one]
  have hyn : (x / algebraMap K L (c₀ : K)) ^ n = 1 := by
    rw [div_pow, hxn, hcn, div_one]
  obtain ⟨l', hl', hyl'⟩ := exists_prime_pow_eq n hn2 (x / algebraMap K L (c₀ : K)) hyn l (E1 + E2) hl hyE
  refine ⟨l', hl', ?_⟩
  have hdiv := minpoly.dvd K x (p := (X ^ (l' ^ padicValNat l' n) -
    C ((c₀ : K) ^ (l' ^ padicValNat l' n)) : K[X])) ?_
  · rwa [← hmin] at hdiv
  · rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_pow, sub_eq_zero]
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero _ hcL)] at hyl'
    exact hyl'
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.E4
