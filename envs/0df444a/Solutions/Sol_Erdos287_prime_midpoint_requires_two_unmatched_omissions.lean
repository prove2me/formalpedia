-- Prove2me | solution 1 for Erdos287.prime_midpoint_requires_two_unmatched_omissions
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T12:53:00.944824+00:00
-- url     : https://prove2.me/submissions/a3df2227-e7a1-4e40-a2c1-94c8055b0450

import Mathlib
import Theorems.Thm_Erdos287_prime_neighbor_support_for_unit_reciprocal_sums
import Theorems.Thm_Erdos287_reflected_omissions_and_boundary_residue
import Theorems.Thm_Erdos287_reciprocal_clearing_and_modular_reduction

open Finset

set_option autoImplicit false

private theorem positive_multiple_below_double (p n : ℕ) (hn : 0 < n)
    (hbound : n < 2 * p) (hd : p ∣ n) : n = p := by
  obtain ⟨c, rfl⟩ := hd
  have hc : 0 < c := by
    by_contra! hbad
    have hz : c = 0 := by omega
    simp [hz] at hn
  have hc' : c < 2 := by
    by_contra! hbad
    have hprod := Nat.mul_le_mul_left p hbad
    rw [Nat.mul_comm p 2] at hprod
    exact hbound.not_ge hprod
  have h : c = 1 := by omega
  simp [h]

/-- If a prime is the midpoint, spacing forces its two neighbors to be
selected. The omitted nonmultiples must have at least two unmatched holes. -/
theorem solution (D : Finset ℕ) (m M p : ℕ) (hm : 1 < m) (hspan : m < M)
    (hp : p.Prime) (hcenter : m + M = 2 * p)
    (hD : D ⊆ Finset.Icc m M) (hsum : ∑ n ∈ D, (1 : ℚ) / n = 1)
    (hcover : ∀ n, m ≤ n → n + 1 ≤ M → n ∈ D ∨ n + 1 ∈ D) :
    let H := ((Finset.Icc m M).filter (fun n => ¬ p ∣ n)) \ D
    2 ≤ (H.filter (fun n => m + M - n ∉ H)).card := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  intro H
  let A := H.filter (fun n => m + M - n ∉ H)
  have hM : M < 2 * p := by omega
  have hodd : 2 < p := by omega
  obtain ⟨hpo, hleft, _⟩ := (Erdos287.prime_neighbor_support_for_unit_reciprocal_sums
    D m M (by omega) hD hsum hcover).2 p hp hM
  have hpred : p - 1 ∈ D := hleft (by omega) (by omega)
  have hgood (n : ℕ) (hn : n ∈ D) : ¬ p ∣ n := by
    intro hd
    obtain ⟨hl, hu⟩ := mem_Icc.mp (hD hn)
    have he := positive_multiple_below_double p n (by omega) (hu.trans_lt hM) hd
    exact hpo (he ▸ hn)
  let U := (Icc m M).filter (fun n => ¬ p ∣ n)
  have hsubset : D ⊆ U := fun n hn => mem_filter.mpr ⟨hD hn, hgood n hn⟩
  have hmultip : p ∣ m + M := by rw [hcenter]; exact dvd_mul_left p 2
  let L := ∏ n ∈ D, n
  have hL : 0 < L := prod_pos (fun n hn => (by have := (mem_Icc.mp (hD hn)).1; omega))
  have hcop : L.Coprime p := Nat.coprime_prod_left_iff.mpr
    (fun n hn => (hp.coprime_iff_not_dvd.mpr (hgood n hn)).symm)
  have hmod := Erdos287.reciprocal_clearing_and_modular_reduction D p L hL hcop
    (fun n hn => dvd_prod_of_mem id hn)
  have hD1 := hmod.2.mpr (by rw [hmod.1.mp hsum])
  have hcut := (Erdos287.reflected_omissions_and_boundary_residue D m M p hp hodd hmultip).2
  change (∑ n ∈ A, (n : ZMod p)⁻¹) - (∑ n ∈ D \ U, (n : ZMod p)⁻¹) =
    -(∑ n ∈ D, (n : ZMod p)⁻¹) at hcut
  have hres : (∑ n ∈ A, (n : ZMod p)⁻¹) = -1 := by
    simpa only [sdiff_eq_empty_iff_subset.mpr hsubset, sum_empty, sub_zero, hD1] using hcut
  change 2 ≤ A.card
  have hne : A.Nonempty := by
    by_contra h
    have he : A = ∅ := not_nonempty_iff_eq_empty.mp h
    rw [he, sum_empty] at hres
    have hz : (1 : ZMod p) = 0 := by
      simpa only [neg_zero, neg_neg] using (congrArg (fun z : ZMod p => -z) hres).symm
    exact one_ne_zero hz
  by_contra! hbad
  have hc : A.card = 1 := by
    have := card_pos.mpr hne
    omega
  obtain ⟨n, hA⟩ := card_eq_one.mp hc
  have hnA : n ∈ A := by simp [hA]
  have hnH : n ∈ H := (mem_filter.mp hnA).1
  obtain ⟨hnI, hnD⟩ := mem_sdiff.mp hnH
  obtain ⟨hnl, hnu⟩ := mem_Icc.mp (mem_filter.mp hnI).1
  have hnInv : (n : ZMod p)⁻¹ = -1 := by simpa [hA] using hres
  have hnMod : (n : ZMod p) = -1 := by
    simpa using congrArg (fun x : ZMod p => x⁻¹) hnInv
  have hdiv : p ∣ n + 1 := by
    apply (ZMod.natCast_eq_zero_iff (n + 1) p).mp
    rw [Nat.cast_add, Nat.cast_one, hnMod, neg_add_cancel]
  have hnEq := positive_multiple_below_double p (n + 1) (by omega) (by omega) hdiv
  have hpredEq : n = p - 1 := by omega
  exact hnD (hpredEq.symm ▸ hpred)

