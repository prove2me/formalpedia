-- Prove2me | solution 1 for FuzzyGames.TUCore.core_eq_superdiff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:29:38.816888+00:00
-- url     : https://prove2.me/submissions/63c04ed3-e0fd-4ee8-96f8-611e041cd73e

import Mathlib
import Definitions.Def_FuzzyGames_TUCore_Basic

set_option autoImplicit false
open FuzzyGames.TUCore

theorem solution {n : ℕ} (v : (Fin n → ℝ) → ℝ) (hv : IsFuzzyTUGame v) :
    fuzzyCore v = superdiff v (FuzzyGames.NTUCore.coal Finset.univ) := by
  obtain ⟨h0, hh⟩ := hv
  ext c
  simp only [fuzzyCore, superdiff, Set.mem_setOf_eq]
  have hcoal : ∀ i : Fin n, FuzzyGames.NTUCore.coal (Finset.univ : Finset (Fin n)) i = 1 := by
    intro i; simp [FuzzyGames.NTUCore.coal]
  constructor
  · rintro ⟨hsum, hcore⟩ σ hσ
    simp only [hcoal]
    -- σ' = σ / t with t ≥ max σ_i, 1
    set t : ℝ := 1 + ∑ i, σ i with ht
    have hσnn : ∀ i, 0 ≤ σ i := fun i => hσ i
    have hsnn : 0 ≤ ∑ i, σ i := Finset.sum_nonneg (fun i _ => hσnn i)
    have htpos : 0 < t := by linarith
    have hle : ∀ i, σ i ≤ t := by
      intro i
      have : σ i ≤ ∑ j, σ j := Finset.single_le_sum (f := σ) (fun j _ => hσnn j) (Finset.mem_univ i)
      linarith
    set σ' : Fin n → ℝ := t⁻¹ • σ with hσ'
    have hσ'mem : σ' ∈ FuzzyGames.NTUCore.cube n := by
      refine ⟨fun i => ?_, fun i => ?_⟩
      · show 0 ≤ σ' i
        simp only [hσ', Pi.smul_apply, smul_eq_mul]
        exact mul_nonneg (inv_nonneg.2 htpos.le) (hσnn i)
      · show σ' i ≤ 1
        simp only [hσ', Pi.smul_apply, smul_eq_mul]
        rw [inv_mul_le_iff₀ htpos]; linarith [hle i]
    have h1 := hcore σ' hσ'mem
    have hσeq : σ = t • σ' := by
      rw [hσ', smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]
    have hvσ : v σ = t * v σ' := by
      rw [hσeq]
      exact hh t htpos σ' (fun i => hσ'mem.1 i)
    have hsumσ : ∑ i, σ i * c i = t * ∑ i, σ' i * c i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hσeq]; simp [mul_assoc]
    have hvN : v (FuzzyGames.NTUCore.coal Finset.univ) = ∑ i, c i := hsum.symm
    have : ∑ i, c i * (1 - σ i) = ∑ i, c i - ∑ i, σ i * c i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [this, hvN, hsumσ, hvσ]
    nlinarith [h1]
  · intro h
    have hcoal0 : (0 : Fin n → ℝ) ≤ FuzzyGames.NTUCore.coal (Finset.univ : Finset (Fin n)) := by
      intro i; simp [FuzzyGames.NTUCore.coal]
    have hsub : ∀ i, c i * (1 - (0:ℝ)) = c i := by intro i; ring
    have h0' := h 0 le_rfl
    simp only [hcoal, h0, Pi.zero_apply, sub_zero, mul_one] at h0'
    have h2 : (0 : Fin n → ℝ) ≤ (2:ℝ) • FuzzyGames.NTUCore.coal (Finset.univ : Finset (Fin n)) :=
      smul_nonneg (by norm_num) hcoal0
    have h1 := h _ h2
    have hv2 := hh 2 (by norm_num) _ hcoal0
    rw [hv2] at h1
    simp only [hcoal, Pi.smul_apply, smul_eq_mul, mul_one] at h1
    have hs1 : ∑ i, c i * (1 - 2) = -∑ i, c i := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [hs1] at h1
    have hsum : ∑ i, c i = v (FuzzyGames.NTUCore.coal Finset.univ) := by linarith
    refine ⟨hsum, fun τ hτ => ?_⟩
    have h3 := h τ (fun i => hτ.1 i)
    simp only [hcoal] at h3
    have : ∑ i, c i * (1 - τ i) = ∑ i, c i - ∑ i, τ i * c i := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i _; ring
    rw [this] at h3
    linarith
