-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mem_e3SB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:46.231631+00:00
-- url     : https://prove2.me/submissions/468d4979-4b05-4955-8c61-a7e5b4813f5a

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_CrossFactorCount
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_SquareSetMemExceptionalUnion
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_primeToPart_eq_self_of_not_dvd
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_e3I
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_mem_e3C
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
    (hcond : ∀ d ∈ Finset.Icc 1 N,
      l ^ (4 * padicValNat l (Fintype.card K ^ d - 1)) ≤ Fintype.card K ^ d)
    {δ δ' : ℕ} (hδ' : 1 ≤ δ') (hδδ' : δ' ≤ δ) (hδN : δ ≤ N) {c' : Fin δ → K} {c'' : Fin δ' → K}
    (hi' : Irreducible (monicOf c')) (hi'' : Irreducible (monicOf c''))
    (h0' : (monicOf c').coeff 0 ≠ 0) (h0'' : (monicOf c'').coeff 0 ≠ 0)
    (hd' : monicOf c' ∣ monicOf c) (hd'' : monicOf c'' ∣ monicOf c) {x y : L}
    (hx : aeval x (monicOf c') = 0) (hy : aeval y (monicOf c'') = 0)
    (hxy : primeToPart l x = primeToPart l y) (hne : x ≠ y)
    (hPne : monicOf c' ≠ monicOf c'') : c ∈ e3SB K L N := by
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hδ1 : 1 ≤ δ := hδ'.trans hδδ'
  have hn : ∀ d, 1 ≤ d → Fintype.card K ^ d - 1 ≠ 0 := fun d hd => by
    have : Fintype.card K ^ 1 ≤ Fintype.card K ^ d := Nat.pow_le_pow_right (by omega) hd
    rw [pow_one] at this
    omega
  have hxp := pow_card_pow_sub_one_eq_one_of_aeval_monicOf hi' h0' hx
  have hyp := pow_card_pow_sub_one_eq_one_of_aeval_monicOf hi'' h0'' hy
  have hldiv : l ∣ Fintype.card K ^ δ - 1 ∨ l ∣ Fintype.card K ^ δ' - 1 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    calc x = primeToPart l x := (primeToPart_eq_self_of_not_dvd hl (hn δ hδ1) hxp hcon.1).symm
      _ = primeToPart l y := hxy
      _ = y := primeToPart_eq_self_of_not_dvd hl (hn δ' hδ') hyp hcon.2
  have hcop : IsCoprime (monicOf c') (monicOf c'') := by
    rw [hi'.coprime_iff_not_dvd]
    intro hdvd
    exact hPne (eq_of_monic_of_associated (monicOf_monic _) (monicOf_monic _)
      (hi'.associated_of_dvd hi'' hdvd))
  simp only [e3SB, Set.mem_iUnion]
  refine ⟨δ, Finset.mem_Icc.2 ⟨hδ1, hδN⟩, δ', Finset.mem_Icc.2 ⟨hδ', hδδ'⟩, l, ?_, c'',
    mem_e3I.2 ⟨hi'', h0''⟩, c', (mem_e3C L).2 ⟨hi', h0', x,
      mem_rootSet.2 ⟨(monicOf_monic _).ne_zero, hx⟩, y,
      mem_rootSet.2 ⟨(monicOf_monic _).ne_zero, hy⟩, hxy⟩, hc, hcop.mul_dvd hd' hd''⟩
  rw [e3PB, Finset.mem_filter, Finset.mem_union, Nat.mem_primeFactors, Nat.mem_primeFactors]
  refine ⟨?_, hcond δ (Finset.mem_Icc.2 ⟨hδ1, hδN⟩)⟩
  rcases hldiv with h | h
  · exact Or.inl ⟨hl, h, hn δ hδ1⟩
  · exact Or.inr ⟨hl, h, hn δ' hδ'⟩
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
