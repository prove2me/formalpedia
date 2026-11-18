-- Prove2me | solution 1 for CompDesignBFM.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:47:02.234347+00:00
-- url     : https://prove2.me/submissions/392c7993-135d-40f3-96dc-6aa4ec15a6d4

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesignBFM_pot

open CompDesignBFM

theorem solution {n : ℕ} (F : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hF0 : F ∅ = 0) (hF : IsMonotoneSF F) (hc : ∀ i, 0 ≤ c i) (S : Finset (Fin n))
    (hS : ∀ T, pot F B c T ≤ pot F B c S) (hS₀ : S = ∅ ∨ 0 < pot F B c S) :
    IsPNE F B c S := by
  have hfac0 : ∀ T : Finset (Fin n), 0 ≤ ∏ i ∈ T, max (1 - c i / B) 0 :=
    fun T => Finset.prod_nonneg fun i _ => le_max_right _ _
  have hFnn : ∀ T, 0 ≤ F T := fun T => hF0 ▸ hF ∅ T (Finset.empty_subset T)
  rcases hS₀ with rfl | hpos
  · -- S = ∅
    refine ⟨fun i hi => absurd hi (Finset.notMem_empty i), ?_⟩
    intro i _
    have h1 := hS {i}
    have hpot0 : pot F B c ∅ = 0 := by simp [pot, hF0]
    rw [hpot0] at h1
    simp only [pot, Finset.prod_singleton] at h1
    unfold mcPay
    by_cases hFi : 0 < F (insert i ∅)
    · rw [if_pos ⟨Finset.mem_insert_self _ _, hFi⟩]
      have hset : (insert i (∅ : Finset (Fin n))) = {i} := by simp
      have hFi' : 0 < F {i} := by rw [← hset]; exact hFi
      have hmx : max (1 - c i / B) 0 ≤ 0 := by
        by_contra hcon
        push Not at hcon
        have := mul_pos hFi' hcon
        linarith
      have hc1 : 1 - c i / B ≤ 0 := le_trans (le_max_left _ _) hmx
      have hcB : B ≤ c i := by
        have : 1 ≤ c i / B := by linarith
        rwa [le_div_iff₀ hB, one_mul] at this
      have e : (insert i (∅ : Finset (Fin n))).erase i = ∅ := by simp
      rw [e, hF0]
      have hFi2 : F (insert i ∅) ≠ 0 := hFi.ne'
      have : B * (F (insert i ∅) - 0) / F (insert i ∅) = B := by
        rw [sub_zero]; field_simp
      rw [this]; exact hcB
    · rw [if_neg (fun h => hFi h.2)]
      exact hc i
  · have hFS : 0 < F S := by
      by_contra hcon
      push Not at hcon
      have := mul_nonpos_of_nonpos_of_nonneg hcon (hfac0 S)
      unfold pot at hpos
      linarith
    have hprodS : 0 < ∏ i ∈ S, max (1 - c i / B) 0 := by
      by_contra hcon
      push Not at hcon
      have := mul_nonpos_of_nonneg_of_nonpos hFS.le hcon
      unfold pot at hpos
      linarith
    constructor
    · intro i hi
      have h1 := hS (S.erase i)
      have hsplit : ∏ j ∈ S, max (1 - c j / B) 0 =
          max (1 - c i / B) 0 * ∏ j ∈ S.erase i, max (1 - c j / B) 0 :=
        (Finset.mul_prod_erase S _ hi).symm
      have hpe : 0 < ∏ j ∈ S.erase i, max (1 - c j / B) 0 := by
        rcases (hfac0 (S.erase i)).lt_or_eq with h | h
        · exact h
        · rw [hsplit, ← h] at hprodS; simp at hprodS
      have hmi : 0 < max (1 - c i / B) 0 := by
        rcases (le_max_right (1 - c i / B) 0).lt_or_eq with h | h
        · exact h
        · rw [hsplit, ← h] at hprodS; simp at hprodS
      have hci : 0 < 1 - c i / B := by
        by_contra hcon
        push Not at hcon
        rw [max_eq_right hcon] at hmi
        exact lt_irrefl _ hmi
      rw [max_eq_left hci.le] at hsplit
      simp only [pot] at h1
      rw [hsplit] at h1
      have h2 : F (S.erase i) ≤ F S * (1 - c i / B) := by
        by_contra hcon
        push Not at hcon
        have := mul_lt_mul_of_pos_right hcon hpe
        nlinarith
      unfold mcPay
      rw [if_pos ⟨hi, hFS⟩, le_div_iff₀ hFS]
      have : F S * (1 - c i / B) = F S - F S * c i / B := by field_simp
      rw [this] at h2
      have h3 : F S * c i / B ≤ F S - F (S.erase i) := by linarith
      rw [div_le_iff₀ hB] at h3
      nlinarith
    · intro i hi
      have h1 := hS (insert i S)
      have hpi : ∏ j ∈ insert i S, max (1 - c j / B) 0 =
          max (1 - c i / B) 0 * ∏ j ∈ S, max (1 - c j / B) 0 := Finset.prod_insert hi
      simp only [pot] at h1
      rw [hpi] at h1
      unfold mcPay
      by_cases hFi : 0 < F (insert i S)
      · rw [if_pos ⟨Finset.mem_insert_self _ _, hFi⟩, Finset.erase_insert hi, div_le_iff₀ hFi]
        have h2 : F (insert i S) * max (1 - c i / B) 0 ≤ F S := by
          by_contra hcon
          push Not at hcon
          have := mul_lt_mul_of_pos_right hcon hprodS
          nlinarith
        have h3 : F (insert i S) * (1 - c i / B) ≤ F S :=
          le_trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hFi.le) h2
        have : F (insert i S) * (1 - c i / B) = F (insert i S) - F (insert i S) * c i / B := by
          field_simp
        rw [this] at h3
        have h4 : F (insert i S) - F S ≤ F (insert i S) * c i / B := by linarith
        rw [le_div_iff₀ hB] at h4
        nlinarith
      · rw [if_neg (fun h => hFi h.2)]
        exact hc i
