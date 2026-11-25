-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.root_set_group
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:16:40.147098+00:00
-- url     : https://prove2.me/submissions/a25a3de8-ada0-43aa-b949-5e1d456c4d66

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_EigenbasisOfDistinctRoots
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_PropositionOneCentralCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRDivisorDegreeSubSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleProbSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeRecipSum
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaLWeight
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRLemmaP
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRTypeCountExact
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCycleTypeProb
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
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
open Finset
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : RootSetGroup := by
  intro n K _ _ _ _ Φ EE hlt htrans hEE hnot
  classical
  have hm : ∀ u : Matrix n n K, u ∈ rootSet' Φ ↔
      (∀ a, u a a = 1) ∧ ∀ a b, a ≠ b → (a, b) ∉ Φ → u a b = 0 := fun u => Iff.rfl
  have hterm : ∀ u ∈ rootSet' (K := K) Φ, ∀ u' ∈ rootSet' (K := K) Φ, ∀ a b c,
      ¬ ((a, c) ∈ Φ ∧ (c, b) ∈ Φ) → c ≠ a → c ≠ b → u a c * u' c b = 0 := by
    intro u hu u' hu' a b c h hca hcb
    rw [hm] at hu hu'
    by_cases h1 : (a, c) ∈ Φ
    · rw [hu'.2 c b hcb (fun h2 => h ⟨h1, h2⟩), mul_zero]
    · rw [hu.2 a c (Ne.symm hca) h1, zero_mul]
  have hmul : ∀ u ∈ rootSet' (K := K) Φ, ∀ u' ∈ rootSet' (K := K) Φ, u * u' ∈ rootSet' Φ ∧
      ∀ x ∈ EE, (u * u') x.1 x.2 = u x.1 x.2 + u' x.1 x.2 := by
    intro u hu u' hu'
    have hu1 := (hm u).1 hu
    have hu1' := (hm u').1 hu'
    refine ⟨(hm _).2 ⟨fun a => ?_, fun a b hab hΦ => ?_⟩, fun x hx => ?_⟩
    · rw [Matrix.mul_apply, Finset.sum_eq_single a]
      · rw [hu1.1, hu1'.1, mul_one]
      · intro c _ hca
        refine hterm u hu u' hu' a a c (fun h => ?_) hca hca
        exact absurd (lt_trans (hlt _ h.1) (hlt _ h.2)) (lt_irrefl a)
      · simp
    · rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro c _
      by_cases hca : c = a
      · subst hca
        rw [hu1'.2 c b hab hΦ, mul_zero]
      by_cases hcb : c = b
      · subst hcb
        rw [hu1.2 a c hab hΦ, zero_mul]
      exact hterm u hu u' hu' a b c (fun h => hΦ (htrans a c b h.1 h.2)) hca hcb
    · have hxΦ := hEE hx
      have hne : x.1 ≠ x.2 := (hlt x hxΦ).ne
      rw [Matrix.mul_apply, Fintype.sum_eq_add x.1 x.2 hne]
      · rw [hu1.1, hu1'.1, one_mul, mul_one, add_comm]
      · rintro c ⟨hca, hcb⟩
        refine hterm u hu u' hu' x.1 x.2 c (fun h => ?_) hca hcb
        exact hnot x.1 c x.2 h.1 h.2 (by simpa using hx)
  have hone : (1 : Matrix n n K) ∈ rootSet' Φ :=
    (hm _).2 ⟨fun a => Matrix.one_apply_eq a, fun a b hab _ => Matrix.one_apply_ne hab⟩
  have hpow : ∀ u ∈ rootSet' (K := K) Φ, ∀ k : ℕ, u ^ k ∈ rootSet' (K := K) Φ := by
    intro u hu k
    induction k with
    | zero => rw [pow_zero]; exact hone
    | succ k ih => rw [pow_succ]; exact (hmul _ ih _ hu).1
  refine ⟨hone, hmul, fun u hu => ?_, ?_⟩
  · have hu1 := (hm u).1 hu
    have htri : u.BlockTriangular id := by
      intro i j hji
      exact hu1.2 i j (ne_of_gt hji) (fun h => absurd (hlt _ h) (not_lt.2 (le_of_lt hji)))
    have hdet : u.det = 1 := by
      rw [Matrix.det_of_upperTriangular htri]
      simp [hu1.1]
    have hunit : IsUnit u := (Matrix.isUnit_iff_isUnit_det u).2 (by rw [hdet]; exact isUnit_one)
    obtain ⟨k, hk, hku⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_finite hunit.unit)
    have hku' : u ^ k = 1 := by
      have := congrArg (fun w : (Matrix n n K)ˣ => (w : Matrix n n K)) hku
      simpa using this
    refine ⟨u ^ (k - 1), hpow u hu _, ?_, ?_⟩
    · rw [← pow_succ', Nat.sub_add_cancel hk, hku']
    · rw [← pow_succ, Nat.sub_add_cancel hk, hku']
  · let e : (rootSet' (K := K) Φ) ≃ (Φ → K) :=
      { toFun := fun u p => (u : Matrix n n K) p.1.1 p.1.2
        invFun := fun f => ⟨Matrix.of fun a b => if a = b then 1 else
            if h : (a, b) ∈ Φ then f ⟨(a, b), h⟩ else 0,
          (hm _).2 ⟨fun a => by simp, fun a b hab hΦ => by simp [hab, hΦ]⟩⟩
        left_inv := fun u => by
          have hu1 := (hm _).1 u.2
          apply Subtype.ext
          ext a b
          by_cases hab : a = b
          · subst hab
            simp [hu1.1]
          · by_cases hΦ : (a, b) ∈ Φ
            · simp [hab, hΦ]
            · simp [hab, hΦ, hu1.2 a b hab hΦ]
        right_inv := fun f => by
          funext p
          have hne : p.1.1 ≠ p.1.2 := (hlt p.1 p.2).ne
          simp [hne] }
    rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_coe]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
