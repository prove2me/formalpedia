-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.square_set_mem_exceptional_union
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:52:01.024235+00:00
-- url     : https://prove2.me/submissions/056bfa57-fd9c-47bf-a6cc-7ec2e8d4a3fa

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_primeToPart_eq_self_of_not_dvd
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_e3A
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_exists_irr_factor
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_e3SB
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_Equi_trans
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_succ_zero
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_succ
import Theorems.Thm_Formalism_GaloisIrreducibility_BorderedIndexCases_bord_zero_zero
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree
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


section
open Finset Polynomial
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
section sets
variable (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
variable {K L}
private theorem ne_zero_of_aeval_eq_zero_of_coeff_zero_ne_zero {F E : Type} [Field F] [Field E] [Algebra F E] {f : F[X]}
    (h0 : f.coeff 0 ≠ 0) {x : E} (hx : aeval x f = 0) : x ≠ 0 := by
  rintro rfl
  apply h0
  rw [← coeff_zero_eq_aeval_zero'] at hx
  exact (algebraMap F E).injective (hx.trans (map_zero _).symm)
private theorem pow_card_pow_eq_self_of_aeval_monicOf_irreducible {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E]
    {δ : ℕ} {c : Fin δ → F} (hi : Irreducible (monicOf c)) {x : E}
    (hx : aeval x (monicOf c) = 0) : x ^ (Fintype.card F ^ δ) = x := by
  have hint : IsIntegral F x := ⟨monicOf c, monicOf_monic c, by rwa [← aeval_def]⟩
  have hmin : minpoly F x = monicOf c :=
    (minpoly.eq_of_irreducible_of_monic hi hx (monicOf_monic c)).symm
  haveI : FiniteDimensional F (IntermediateField.adjoin F ({x} : Set E)) :=
    IntermediateField.adjoin.finiteDimensional hint
  have hfr : Module.finrank F (IntermediateField.adjoin F ({x} : Set E)) = δ := by
    rw [IntermediateField.adjoin.finrank hint, hmin, monicOf_natDegree]
  haveI : Finite (IntermediateField.adjoin F ({x} : Set E)) := Module.finite_of_finite F
  letI : Fintype (IntermediateField.adjoin F ({x} : Set E)) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin F ({x} : Set E)) = Fintype.card F ^ δ := by
    rw [Module.card_eq_pow_finrank (K := F), hfr]
  have key := FiniteField.pow_card
    (⟨x, IntermediateField.mem_adjoin_simple_self F x⟩ : IntermediateField.adjoin F ({x} : Set E))
  rw [hcard] at key
  simpa using congrArg (fun y : IntermediateField.adjoin F ({x} : Set E) => (y : E)) key
private theorem pow_card_pow_sub_one_eq_one_of_aeval_monicOf {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E]
    {δ : ℕ} {c : Fin δ → F} (hi : Irreducible (monicOf c)) (h0 : (monicOf c).coeff 0 ≠ 0)
    {x : E} (hx : aeval x (monicOf c) = 0) : x ^ (Fintype.card F ^ δ - 1) = 1 := by
  have hx0 : x ≠ 0 := ne_zero_of_aeval_eq_zero_of_coeff_zero_ne_zero h0 hx
  have hq : 1 ≤ Fintype.card F ^ δ := Nat.one_le_pow _ _ Fintype.card_pos
  have h := pow_card_pow_eq_self_of_aeval_monicOf_irreducible hi hx
  rw [← Nat.sub_add_cancel hq, pow_succ] at h
  exact mul_right_cancel₀ hx0 (h.trans (one_mul x).symm)
end sets
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

set_option autoImplicit false
open Finset Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable (K L : Type) [Field K] [Fintype K] [Field L] [Algebra K L] [IsAlgClosed L]
variable {K L}
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {N : ℕ} {c : Fin N → K} (hc : c ∈ sqSet K N) {l : ℕ} (hl : l.Prime)
    (hlBB : l ∉ BB (Fintype.card K) N)
    (hninj : ¬ Set.InjOn (primeToPart l) ((monicOf c).rootSet L)) :
    c ∈ e3SA K L N ∪ e3SB K L N := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hcs : Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0 := by
    simpa [sqSet] using hc
  have hf0 : monicOf c ≠ 0 := (monicOf_monic c).ne_zero
  have hcond : ∀ d ∈ Finset.Icc 1 N,
      l ^ (4 * padicValNat l (Fintype.card K ^ d - 1)) ≤ Fintype.card K ^ d := by
    intro d hd
    have hd' := Finset.mem_Icc.1 hd
    by_contra hlt
    push_neg at hlt
    have hqd : 1 ≤ Fintype.card K ^ d := Nat.one_le_pow _ _ (by omega)
    have hv : padicValNat l (Fintype.card K ^ d - 1) ≠ 0 := by
      intro hv
      rw [hv, mul_zero, pow_zero] at hlt
      omega
    have hpos : Fintype.card K ^ d - 1 ≠ 0 := by
      intro h
      rw [h, padicValNat.zero] at hv
      exact hv rfl
    have hldvd : l ∣ Fintype.card K ^ d - 1 := dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.2 hv)
    have hle : l ≤ Fintype.card K ^ d - 1 := Nat.le_of_dvd (by omega) hldvd
    have hdN : Fintype.card K ^ d ≤ Fintype.card K ^ N := Nat.pow_le_pow_right (by omega) hd'.2
    apply hlBB
    apply Finset.mem_insert_of_mem
    have hmem : l ∈ (Finset.range (Fintype.card K ^ N + 1)).filter (fun l => l.Prime ∧
        ∃ d ∈ Finset.Icc 1 N, Fintype.card K ^ d < l ^ (4 * padicValNat l (Fintype.card K ^ d - 1))) :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hl, d, hd, hlt⟩
    convert hmem
  simp only [Set.InjOn] at hninj
  push_neg at hninj
  obtain ⟨x, hxr, y, hyr, hxy, hne⟩ := hninj
  have hxa : aeval x (monicOf c) = 0 := (mem_rootSet.1 hxr).2
  have hya : aeval y (monicOf c) = 0 := (mem_rootSet.1 hyr).2
  obtain ⟨δ1, h1δ1, hδ1N, c1, hi1, h01, hd1, hx1⟩ := exists_irr_factor hf0 hcs.2 hxa
  obtain ⟨δ2, h1δ2, hδ2N, c2, hi2, h02, hd2, hy2⟩ := exists_irr_factor hf0 hcs.2 hya
  rw [monicOf_natDegree] at hδ1N hδ2N
  by_cases heq : monicOf c1 = monicOf c2
  · left
    have hy1 : aeval y (monicOf c1) = 0 := by rw [heq]; exact hy2
    have hn : Fintype.card K ^ δ1 - 1 ≠ 0 := by
      have : Fintype.card K ^ 1 ≤ Fintype.card K ^ δ1 := Nat.pow_le_pow_right (by omega) h1δ1
      rw [pow_one] at this
      omega
    have hldvd : l ∣ Fintype.card K ^ δ1 - 1 := by
      by_contra hcon
      apply hne
      calc x = primeToPart l x :=
            (primeToPart_eq_self_of_not_dvd hl hn (pow_card_pow_sub_one_eq_one_of_aeval_monicOf hi1 h01 hx1) hcon).symm
        _ = primeToPart l y := hxy
        _ = y := primeToPart_eq_self_of_not_dvd hl hn (pow_card_pow_sub_one_eq_one_of_aeval_monicOf hi1 h01 hy1) hcon
    have h2δ1 : 2 ≤ δ1 := by
      by_contra hlt
      obtain rfl : δ1 = 1 := by omega
      apply hne
      simp [monicOf] at hx1 hy1
      linear_combination hx1 - hy1
    simp only [e3SA, Set.mem_iUnion]
    refine ⟨δ1, Finset.mem_Icc.2 ⟨h2δ1, hδ1N⟩, l, ?_, c1, (mem_e3A L).2 ⟨hi1, ?_⟩, hc, hd1⟩
    · rw [e3PA, Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hl, hldvd, hn⟩, hcond δ1 (Finset.mem_Icc.2 ⟨h1δ1, hδ1N⟩)⟩
    · intro hinj
      exact hne (hinj (mem_rootSet.2 ⟨(monicOf_monic _).ne_zero, hx1⟩)
        (mem_rootSet.2 ⟨(monicOf_monic _).ne_zero, hy1⟩) hxy)
  · right
    rcases le_total δ2 δ1 with h21 | h12
    · exact mem_e3SB hc hl hcond h1δ2 h21 hδ1N hi1 hi2 h01 h02 hd1 hd2 hx1 hy2 hxy hne heq
    · exact mem_e3SB hc hl hcond h1δ1 h12 hδ2N hi2 hi1 h02 h01 hd2 hd1 hy2 hx1 hxy.symm
        (Ne.symm hne) (Ne.symm heq)
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
