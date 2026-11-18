-- Prove2me | solution 1 for CompDesign.thm_4_1_potential_increases
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:33:51.798603+00:00
-- url     : https://prove2.me/submissions/77e7f7d6-8d2d-4d29-b81d-7525ef00fde3

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_mcPay
import Definitions.Def_CompDesign_util
import Definitions.Def_CompDesign_IsStrictImprovement
import Definitions.Def_CompDesign_PhiLex

open CompDesignBFM

lemma optin {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ j, 0 ≤ c j)
    (hcB : ∀ j, c j < B) (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) :
    (CompDesign.util v B c S i < CompDesign.util v B c (insert i S) i → 0 < v (insert i S)) ∧
    (CompDesign.util v B c S i < CompDesign.util v B c (insert i S) i ↔
      c i < mcPay v B (insert i S) i) ∧
    (0 < v (insert i S) →
      (c i < mcPay v B (insert i S) i ↔ v S < (1 - c i / B) * v (insert i S))) := by
  have hu0 : CompDesign.util v B c S i = 0 := by simp [CompDesign.util, hi]
  have hu1 : CompDesign.util v B c (insert i S) i = mcPay v B (insert i S) i - c i := by
    simp [CompDesign.util]
  have hiff : CompDesign.util v B c S i < CompDesign.util v B c (insert i S) i ↔
      c i < mcPay v B (insert i S) i := by
    rw [hu0, hu1]; constructor <;> intro h <;> linarith
  refine ⟨?_, hiff, ?_⟩
  · intro h
    rw [hiff] at h
    by_contra hv
    have : mcPay v B (insert i S) i = 0 := by
      simp [mcPay, hv]
    have := hc i
    linarith
  · intro hpos
    have hmc : mcPay v B (insert i S) i = B * (v (insert i S) - v S) / v (insert i S) := by
      simp [mcPay, hpos, Finset.erase_insert hi]
    rw [hmc, lt_div_iff₀ hpos]
    have hB' : (1 - c i / B) * v (insert i S) = v (insert i S) - c i * v (insert i S) / B := by
      field_simp
    rw [hB']
    constructor
    · intro h
      have : c i * v (insert i S) / B < v (insert i S) - v S := by
        rw [div_lt_iff₀ hB]; linarith
      linarith
    · intro h
      have : c i * v (insert i S) / B < v (insert i S) - v S := by linarith
      rw [div_lt_iff₀ hB] at this
      linarith

lemma optout {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ j, 0 ≤ c j)
    (hcB : ∀ j, c j < B) (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) (hpos : 0 < v S) :
    (CompDesign.util v B c S i < CompDesign.util v B c (S.erase i) i ↔ mcPay v B S i < c i) ∧
    (mcPay v B S i < c i ↔ (1 - c i / B) * v S < v (S.erase i)) := by
  have hu0 : CompDesign.util v B c S i = mcPay v B S i - c i := by
    simp [CompDesign.util, hi]
  have hu1 : CompDesign.util v B c (S.erase i) i = 0 := by
    simp [CompDesign.util]
  refine ⟨?_, ?_⟩
  · rw [hu0, hu1]; constructor <;> intro h <;> linarith
  · have hmc : mcPay v B S i = B * (v S - v (S.erase i)) / v S := by
      simp [mcPay, hi, hpos]
    rw [hmc, div_lt_iff₀ hpos]
    have hB' : (1 - c i / B) * v S = v S - c i * v S / B := by field_simp
    rw [hB']
    constructor
    · intro h
      have : v S - v (S.erase i) < c i * v S / B := by
        rw [lt_div_iff₀ hB]; linarith
      linarith
    · intro h
      have : v S - v (S.erase i) < c i * v S / B := by linarith
      rw [lt_div_iff₀ hB] at this
      linarith


theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ)
    (hB : 0 < B) (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v)
    (hc : ∀ j, 0 ≤ c j) (hcB : ∀ j, c j < B) (S S' : Finset (Fin n))
    (h : CompDesign.IsStrictImprovement v B c S S') :
    CompDesign.PhiLex v B c S < CompDesign.PhiLex v B c S' := by
  obtain ⟨i, hS', hlt⟩ := h
  have hfac : ∀ j, 0 < 1 - c j / B := by
    intro j
    have : c j / B < 1 := (div_lt_one hB).2 (hcB j)
    linarith
  have hprod : ∀ T : Finset (Fin n), 0 < ∏ j ∈ T, (1 - c j / B) :=
    fun T => Finset.prod_pos fun j _ => hfac j
  have hnn : ∀ T, 0 ≤ v T := fun T => hv0 ▸ hm ∅ T (Finset.empty_subset T)
  unfold CompDesign.PhiLex CompDesign.Phi
  by_cases hi : i ∈ S
  · -- opt out
    have hS'e : S' = S.erase i := by simp [CompDesign.switch, hi] at hS'; exact hS'
    subst hS'e
    have hprodS : ∏ j ∈ S, (1 - c j / B) = (1 - c i / B) * ∏ j ∈ S.erase i, (1 - c j / B) :=
      (Finset.mul_prod_erase S _ hi).symm
    have hsum : ∑ j ∈ S, c j = c i + ∑ j ∈ S.erase i, c j := (Finset.add_sum_erase S c hi).symm
    by_cases hpos : 0 < v S
    · obtain ⟨h1, h2⟩ := optout v B c hB hv0 hm hs hc hcB S i hi hpos
      have hI : CompDesign.util v B c S i < CompDesign.util v B c (S.erase i) i := hlt
      have hd : (1 - c i / B) * v S < v (S.erase i) := h2.1 (h1.1 hI)
      rw [Prod.Lex.toLex_lt_toLex]
      left
      simp only
      rw [hprodS]
      have := hprod (S.erase i)
      nlinarith
    · have hv : v S = 0 := le_antisymm (not_lt.1 hpos) (hnn S)
      have hv' : v (S.erase i) = 0 :=
        le_antisymm (hv ▸ hm _ _ (Finset.erase_subset i S)) (hnn _)
      have hI : CompDesign.util v B c S i < CompDesign.util v B c (S.erase i) i := hlt
      have hci : 0 < c i := by
        have e1 : CompDesign.util v B c S i = mcPay v B S i - c i := by
          simp [CompDesign.util, hi]
        have e2 : CompDesign.util v B c (S.erase i) i = 0 := by simp [CompDesign.util]
        have e3 : mcPay v B S i = 0 := by simp [mcPay, hpos]
        rw [e1, e2, e3] at hI
        linarith
      rw [Prod.Lex.toLex_lt_toLex]
      right
      refine ⟨by simp [hv, hv'], ?_⟩
      simp only
      rw [hsum]
      linarith
  · -- opt in
    have hS'e : S' = insert i S := by simp [CompDesign.switch, hi] at hS'; exact hS'
    subst hS'e
    have hI : CompDesign.util v B c S i < CompDesign.util v B c (insert i S) i := hlt
    obtain ⟨h1, h2, h3⟩ := optin v B c hB hv0 hm hs hc hcB S i hi
    have hpos := h1 hI
    have hd : v S < (1 - c i / B) * v (insert i S) := (h3 hpos).1 (h2.1 hI)
    have hprodS : ∏ j ∈ insert i S, (1 - c j / B) = (1 - c i / B) * ∏ j ∈ S, (1 - c j / B) :=
      Finset.prod_insert hi
    rw [Prod.Lex.toLex_lt_toLex]
    left
    simp only
    rw [hprodS]
    have := hprod S
    nlinarith
