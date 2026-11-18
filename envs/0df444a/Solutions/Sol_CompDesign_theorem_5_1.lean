-- Prove2me | solution 1 for CompDesign.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:36:07.559135+00:00
-- url     : https://prove2.me/submissions/c3dd06e7-20a0-438b-b0e8-a70f956eca6d

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_kappa
import Theorems.Thm_CompDesign_eq_22_23
import Theorems.Thm_CompDesign_thm_5_1_union_bound
import Theorems.Thm_CompDesign_thm_5_1_zero_case
import Theorems.Thm_CompDesign_kappa_le

open CompDesignBFM

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ i, 0 ≤ c i)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1) (hcl : ∀ i, c i ≤ l * B) :
    (∀ S : Finset (Fin n), IsPNE v B c S → OPT v B c ≤ (1 + CompDesign.kappa l) * v S) ∧
    1 + CompDesign.kappa l ≤ (2 - l) / (1 - l) := by
  have hl' : 0 < 1 - l := by linarith
  have hkap := CompDesign.kappa_le l hl0 hl1
  refine ⟨?_, ?_⟩
  · intro S hS
    have hcB : ∀ j, c j < B := fun j => by nlinarith [hcl j]
    have hnn : ∀ T, 0 ≤ v T := fun T => hv0 ▸ hm ∅ T (Finset.empty_subset T)
    by_cases hpos : 0 < v S
    · obtain ⟨T, hT, hTv⟩ := (OPT_isGreatest v hB.le c).1
      have hTfeas : ∑ i ∈ T, c i ≤ B := hT
      have hOPT : OPT v B c = v T := hTv.symm
      obtain ⟨hu1, hu2⟩ := CompDesign.thm_5_1_union_bound v hv0 hm hs S T
      have hterm : ∀ i ∈ T \ S, v (insert i S) - v S ≤ v S * ((c i / B) / (1 - c i / B)) := by
        intro i hi
        have hiS : i ∉ S := (Finset.mem_sdiff.1 hi).2
        have := (CompDesign.eq_22_23 v B c hB hv0 hm hs hc hcB S hS hpos i hiS).2
        linarith
      have hsum : ∑ i ∈ T \ S, (v (insert i S) - v S) ≤
          v S * ∑ i ∈ T \ S, (c i / B) / (1 - c i / B) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum hterm
      -- the family x_j = c_j / B on T \ S, 0 elsewhere
      set x : Fin n → ℝ := fun j => if j ∈ T \ S then c j / B else 0 with hx
      have hx0 : ∀ j, 0 ≤ x j ∧ x j ≤ l := by
        intro j
        simp only [hx]
        split_ifs
        · exact ⟨div_nonneg (hc j) hB.le, by rw [div_le_iff₀ hB]; exact hcl j⟩
        · exact ⟨le_rfl, hl0⟩
      have hxsum : ∑ j, x j ≤ 1 := by
        have : ∑ j, x j = ∑ j ∈ T \ S, c j / B := by
          simp only [hx]
          rw [← Finset.sum_filter]
          congr 1
          ext j; simp
        rw [this, ← Finset.sum_div, div_le_one hB]
        calc ∑ j ∈ T \ S, c j ≤ ∑ j ∈ T, c j :=
              Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun j _ _ => hc j)
          _ ≤ B := hTfeas
      have hf : ∀ j, x j / (1 - x j) =
          if j ∈ T \ S then (c j / B) / (1 - c j / B) else 0 := by
        intro j
        simp only [hx]
        split_ifs <;> simp
      have hxterm : ∑ j, x j / (1 - x j) = ∑ i ∈ T \ S, (c i / B) / (1 - c i / B) := by
        simp_rw [hf]
        rw [Finset.sum_ite_mem, Finset.univ_inter]
      have hmem : ∑ j, x j / (1 - x j) ∈ {s : ℝ | ∃ (m : ℕ) (y : Fin m → ℝ),
          (∀ j, 0 ≤ y j ∧ y j ≤ l) ∧ ∑ j, y j ≤ 1 ∧ s = ∑ j, y j / (1 - y j)} :=
        ⟨n, x, hx0, hxsum, rfl⟩
      have hbdd : BddAbove {s : ℝ | ∃ (m : ℕ) (y : Fin m → ℝ),
          (∀ j, 0 ≤ y j ∧ y j ≤ l) ∧ ∑ j, y j ≤ 1 ∧ s = ∑ j, y j / (1 - y j)} := by
        refine ⟨1 / (1 - l), ?_⟩
        rintro s ⟨m, y, hy, hsum, rfl⟩
        have hterm : ∀ j, y j / (1 - y j) ≤ y j / (1 - l) := by
          intro j
          exact div_le_div_of_nonneg_left (hy j).1 hl' (by linarith [(hy j).2])
        calc ∑ j, y j / (1 - y j) ≤ ∑ j, y j / (1 - l) := Finset.sum_le_sum fun j _ => hterm j
          _ = (∑ j, y j) / (1 - l) := by rw [Finset.sum_div]
          _ ≤ 1 / (1 - l) := div_le_div_of_nonneg_right hsum hl'.le
      have hle : ∑ i ∈ T \ S, (c i / B) / (1 - c i / B) ≤ CompDesign.kappa l := by
        rw [← hxterm]
        exact le_csSup hbdd hmem
      rw [hOPT]
      have h1 : v S * ∑ i ∈ T \ S, (c i / B) / (1 - c i / B) ≤ v S * CompDesign.kappa l :=
        mul_le_mul_of_nonneg_left hle hpos.le
      nlinarith
    · have hzero : v S = 0 := le_antisymm (not_lt.1 hpos) (hnn S)
      rw [CompDesign.thm_5_1_zero_case v B c hB hv0 hm hs hc hcB S hS hzero, hzero]
      simp
  · have : (2 - l) / (1 - l) = 1 + 1 / (1 - l) := by field_simp; ring
    rw [this]; linarith
