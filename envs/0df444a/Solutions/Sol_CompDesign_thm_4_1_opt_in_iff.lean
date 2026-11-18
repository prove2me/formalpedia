-- Prove2me | solution 1 for CompDesign.thm_4_1_opt_in_iff
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:25:09.464854+00:00
-- url     : https://prove2.me/submissions/e49fd2de-0a86-4f2d-86c4-d5a98883050f

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_mcPay
import Definitions.Def_CompDesign_util

open CompDesignBFM

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
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
