-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.squarefree_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:52:02.637746+00:00
-- url     : https://prove2.me/submissions/cc4363eb-38aa-4b60-be12-45a1556bae2f

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRIrredCountUpper
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRSquarefreeCount
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_card_mult_le
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_geom_tail
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_irreducible_count_upper
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_coeff
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_coeffs
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_monic
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_monicOf_natDegree


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution : SquarefreeCount := by
  classical
  intro K _ _ N hN
  set q := Fintype.card K with hq
  have hq2 : 2 ≤ q := Fintype.one_lt_card
  set Ω := (Finset.univ : Finset (Fin N → K)) with hΩ
  set Good := Ω.filter (fun c => Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0) with hGood
  set Bad0 := Ω.filter (fun c => (monicOf c).coeff 0 = 0) with hBad0
  set BadS := Ω.filter (fun c => ¬ Squarefree (monicOf c) ∧ (monicOf c).coeff 0 ≠ 0) with hBadS
  have hΩcard : Ω.card = q ^ N := by simp [hΩ, hq]
  have hcover : Ω ⊆ Good ∪ (Bad0 ∪ BadS) := by
    intro c hc
    simp only [hGood, hBad0, hBadS, Finset.mem_union, Finset.mem_filter]
    by_cases h0 : (monicOf c).coeff 0 = 0
    · exact Or.inr (Or.inl ⟨hc, h0⟩)
    · by_cases hs : Squarefree (monicOf c)
      · exact Or.inl ⟨hc, hs, h0⟩
      · exact Or.inr (Or.inr ⟨hc, hs, h0⟩)
  have hB0 : Bad0.card ≤ q ^ (N - 1) := by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    have hcard : Fintype.card (Fin M → K) = q ^ (M + 1 - 1) := by simp [hq]
    rw [← hcard, ← Finset.card_univ]
    apply Finset.card_le_card_of_injOn (fun c => Fin.tail c)
    · intro c _; exact Finset.mem_coe.mpr (Finset.mem_univ _)
    · intro c hc c' hc' h
      have h0 : c 0 = 0 := by
        have := (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
        rwa [← monicOf_coeff c 0]
      have h0' : c' 0 = 0 := by
        have := (Finset.mem_filter.mp (Finset.mem_coe.mp hc')).2
        rwa [← monicOf_coeff c' 0]
      rw [← Fin.cons_self_tail c, ← Fin.cons_self_tail c', h0, h0']
      exact congrArg (Fin.cons 0) h
  set I : ℕ → ℕ := fun j => ((Finset.univ : Finset (Fin j → K)).filter
      (fun p => Irreducible (monicOf p) ∧ (monicOf p).coeff 0 ≠ 0)).card with hI
  have hBS : BadS.card ≤ ∑ j ∈ Finset.Icc 1 (N / 2), I j * q ^ (N - 2 * j) := by
    have hsub : BadS ⊆ (Finset.Icc 1 (N / 2)).biUnion (fun j =>
        ((Finset.univ : Finset (Fin j → K)).filter
          (fun p => Irreducible (monicOf p) ∧ (monicOf p).coeff 0 ≠ 0)).biUnion (fun p =>
            Ω.filter (fun c => monicOf p * monicOf p ∣ monicOf c))) := by
      intro c hc
      obtain ⟨_, hns, h0⟩ := Finset.mem_filter.mp hc
      have hne : monicOf c ≠ 0 := (monicOf_monic c).ne_zero
      rw [squarefree_iff_irreducible_sq_not_dvd_of_ne_zero hne] at hns
      push Not at hns
      obtain ⟨P, hPirr, hPdvd⟩ := hns
      set P' := normalize P with hP'
      have hass : Associated P' P := normalize_associated P
      have hP'irr : Irreducible P' := hass.symm.irreducible hPirr
      have hP'mon : P'.Monic := monic_normalize hPirr.ne_zero
      have hP'dvd : P' * P' ∣ monicOf c :=
        (mul_dvd_mul hass.dvd hass.dvd).trans hPdvd
      obtain ⟨g, hg⟩ := hP'dvd
      have hgm : g.Monic := (hP'mon.mul hP'mon).of_mul_monic_left (hg ▸ monicOf_monic c)
      have hdeg : (monicOf c).natDegree = (P' * P').natDegree + g.natDegree := by
        rw [hg]; exact (hP'mon.mul hP'mon).natDegree_mul hgm
      rw [monicOf_natDegree, hP'mon.natDegree_mul hP'mon] at hdeg
      have hj1 : 1 ≤ P'.natDegree := hP'irr.natDegree_pos
      have hc0 : P'.coeff 0 ≠ 0 := by
        intro hz
        apply h0
        rw [hg, mul_coeff_zero, mul_coeff_zero, hz]
        simp
      refine Finset.mem_biUnion.mpr ⟨P'.natDegree, Finset.mem_Icc.mpr ⟨hj1, by omega⟩, ?_⟩
      refine Finset.mem_biUnion.mpr ⟨fun i => P'.coeff i, ?_, ?_⟩
      · rw [Finset.mem_filter, monicOf_coeffs hP'mon rfl]
        exact ⟨Finset.mem_univ _, hP'irr, hc0⟩
      · rw [Finset.mem_filter, monicOf_coeffs hP'mon rfl]
        exact ⟨Finset.mem_univ _, ⟨g, hg⟩⟩
    refine (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans ?_)
    apply Finset.sum_le_sum
    intro j _
    refine Finset.card_biUnion_le.trans ?_
    rw [hI]
    simp only
    rw [← smul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro p _
    exact card_mult_le N j (monicOf p) (monicOf_monic p) (monicOf_natDegree p)
  have hI1 : I 1 ≤ q - 1 := by
    have hsub : ((Finset.univ : Finset (Fin 1 → K)).filter
        (fun p => Irreducible (monicOf p) ∧ (monicOf p).coeff 0 ≠ 0)) ⊆
        (Finset.univ : Finset (Fin 1 → K)).erase 0 := by
      intro p hp
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      have := (Finset.mem_filter.mp hp).2.2
      apply this
      have h := monicOf_coeff (0 : Fin 1 → K) 0
      simpa using h
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ] at this
    simpa [hI, hq] using this
  have hI2 : ∀ j, 2 ≤ j → 2 * I j ≤ q ^ j := by
    intro j hj
    have h1 := irreducible_count_upper K j (by omega)
    have h2 : I j ≤ ((Finset.univ : Finset (Fin j → K)).filter
        (fun c => Irreducible (monicOf c))).card := by
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2.1⟩
    calc 2 * I j ≤ j * I j := Nat.mul_le_mul_right _ hj
      _ ≤ j * _ := Nat.mul_le_mul_left _ h2
      _ ≤ q ^ j := h1
  have hsum : ∑ j ∈ Finset.Icc 1 (N / 2), I j * q ^ (N - 2 * j) ≤ q ^ (N - 1) := by
    rcases Nat.lt_or_ge N 2 with hlt | hge
    · have : N / 2 = 0 := by omega
      rw [this]; simp
    · have hm1 : 1 ≤ N / 2 := by omega
      rw [← Finset.add_sum_Ioc_eq_sum_Icc hm1]
      have hIoc : Finset.Ioc 1 (N / 2) = Finset.Icc 2 (N / 2) := by
        ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
      rw [hIoc]
      have h2 : 2 * ∑ j ∈ Finset.Icc 2 (N / 2), I j * q ^ (N - 2 * j) ≤ 2 * q ^ (N - 2) := by
        rw [Finset.mul_sum]
        refine le_trans (Finset.sum_le_sum (fun j hj => ?_)) (geom_tail q N (N / 2) hq2 hge
          (Nat.div_le_self _ _))
        obtain ⟨hj2, hjm⟩ := Finset.mem_Icc.mp hj
        calc 2 * (I j * q ^ (N - 2 * j)) = (2 * I j) * q ^ (N - 2 * j) := by ring
          _ ≤ q ^ j * q ^ (N - 2 * j) := Nat.mul_le_mul_right _ (hI2 j hj2)
          _ = q ^ (N - j) := by rw [← pow_add]; congr 1; omega
      have h3 : I 1 * q ^ (N - 2 * 1) ≤ (q - 1) * q ^ (N - 2) := Nat.mul_le_mul_right _ hI1
      have h4 : q ^ (N - 1) = (q - 1) * q ^ (N - 2) + q ^ (N - 2) := by
        have : N - 1 = (N - 2) + 1 := by omega
        rw [this, pow_succ]
        obtain ⟨r, hr⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
        rw [hr]
        simp only [Nat.add_sub_cancel]
        ring
      omega
  have h1 := Finset.card_le_card hcover
  have h2 := Finset.card_union_le Good (Bad0 ∪ BadS)
  have h3 := Finset.card_union_le Bad0 BadS
  rw [hΩcard] at h1
  have h5 := hBS.trans hsum
  omega
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
