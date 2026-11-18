-- Prove2me | solution 1 for CompDesign.thm_4_1_opt_out_iff
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:25:10.000051+00:00
-- url     : https://prove2.me/submissions/f39ed7ff-0019-40df-8ee6-b9339dd63cea

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_mcPay
import Definitions.Def_CompDesign_util

open CompDesignBFM

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
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
