-- Prove2me | solution 1 for DetANN.lemma_3_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-16T06:47:25.445588+00:00
-- url     : https://prove2.me/submissions/7aab581a-ae44-4eb0-bc29-75c1f6ee90bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_DetANN_DataStructure
import Theorems.Thm_DetANN_HPIM_hpim_query_program
import Theorems.Thm_DetANN_HPIM_hpim_tree_correct
import Theorems.Thm_DetANN_HPIM_hpim_preprocessing

/-!
# `lemma_3_3` from the query program `Q`, the tree correctness `M` and the preprocessing program `P`
-/

open DetANN DetANN.HPIM in
theorem solution :
    ∃ Pre Qry : PNormReg.Program, DetProgram Pre ∧ DetProgram Qry ∧
      ∃ C : ℝ, 1 < C ∧ ∃ K C' : ℕ, ∀ m N : ℕ, 1 ≤ m → 1 ≤ N →
        ∀ Y : Fin N → EuclideanSpace ℝ (Fin m), Function.Injective Y →
          ∀ δ : ℝ, 0 < δ → δ < 1 / 2 →
            IsDetANNStructure Pre Qry Y δ (1 + δ)
              ((C' : ℝ) * ((N : ℝ) + m) ^ K * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K)
              ((C' : ℝ) * N * (C / δ) ^ ((K : ℝ) * m) * Real.log (N / δ) ^ K)
              ((C' : ℝ) * (m : ℝ) ^ 2 * Real.log (N / δ) ^ 2) := by
  obtain ⟨Qry, hQdet, c₀, hQ⟩ := hpim_query_program
  obtain ⟨C₁, hM⟩ := hpim_tree_correct
  obtain ⟨Pre, hPdet, C, hC, K, CP, hP⟩ := hpim_preprocessing
  refine ⟨Pre, Qry, hPdet, hQdet, C, hC, K, max CP (2 * c₀ * C₁), ?_⟩
  intro m N hm hN Y hY δ hδ hδ'
  have hNd : 1 < (N : ℝ) / δ := by
    rw [one_lt_div hδ]; have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlog : 0 < Real.log (N / δ) := Real.log_pos hNd
  have hCP : (CP : ℝ) ≤ (max CP (2 * c₀ * C₁) : ℕ) := by exact_mod_cast le_max_left _ _
  have hCQ : ((2 * c₀ * C₁ : ℕ) : ℝ) ≤ (max CP (2 * c₀ * C₁) : ℕ) := by exact_mod_cast le_max_right _ _
  obtain ⟨t, hhalt, hwork, hcells, hI1, hlay⟩ := hP m N hm hN Y hY δ hδ hδ'
  refine ⟨t, hhalt, ?_, ?_, ?_⟩
  · refine hwork.trans ?_
    have h1 : (0 : ℝ) ≤ ((N : ℝ) + m) ^ K := by positivity
    have h2 : (0 : ℝ) ≤ (C / δ) ^ ((K : ℝ) * m) := by positivity
    have h3 : (0 : ℝ) ≤ Real.log (N / δ) ^ K := pow_nonneg hlog.le _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCP h1) h2) h3
  · refine hcells.trans ?_
    have h1 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have h2 : (0 : ℝ) ≤ (C / δ) ^ ((K : ℝ) * m) := by positivity
    have h3 : (0 : ℝ) ≤ Real.log (N / δ) ^ K := pow_nonneg hlog.le _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCP h1) h2) h3
  · intro q
    obtain ⟨t', hh, hw, hp⟩ := hQ m _ (hpimTree Y δ) q hm hI1 hlay
    obtain ⟨⟨k, hk, hann⟩, hcost⟩ := hM m N hm hN Y hY δ hδ hδ' q
    refine ⟨t', hh, ?_, k, ?_, hann⟩
    · have hw' : ((PNormReg.run Qry (queryState m (PNormReg.run Pre (inputState Y δ) detTape t) q)
          detTape t').work : ℝ) ≤ (c₀ : ℝ) * ((m : ℝ) + 1) * ((hpimTree Y δ).cost q : ℝ) := by
        exact_mod_cast hw
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hc0 : (0 : ℝ) ≤ c₀ := by positivity
      have hL : 0 ≤ Real.log (N / δ) ^ 2 := by positivity
      calc _ ≤ (c₀ : ℝ) * ((m : ℝ) + 1) * ((hpimTree Y δ).cost q : ℝ) := hw'
        _ ≤ (c₀ : ℝ) * ((m : ℝ) + 1) * (C₁ * m * Real.log (N / δ) ^ 2) := by gcongr
        _ ≤ (c₀ : ℝ) * (2 * m) * (C₁ * m * Real.log (N / δ) ^ 2) := by gcongr; linarith
        _ = ((2 * c₀ * C₁ : ℕ) : ℝ) * (m : ℝ) ^ 2 * Real.log (N / δ) ^ 2 := by push_cast; ring
        _ ≤ _ := by gcongr
    · rw [hp, hk]
