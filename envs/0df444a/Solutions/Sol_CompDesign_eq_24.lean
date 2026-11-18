-- Prove2me | solution 1 for CompDesign.eq_24
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:12:20.713021+00:00
-- url     : https://prove2.me/submissions/fd5468d7-bd05-4fe4-ab65-2a7d3ce8b5d7

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_IsPNE
import Theorems.Thm_CompDesign_thm_5_1_union_bound
import Theorems.Thm_CompDesign_eq_22_23

open CompDesignBFM

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ j, 0 ≤ c j)
    (hcB : ∀ j, c j < B) (S : Finset (Fin n)) (hS : IsPNE v B c S) (hpos : 0 < v S)
    (T : Finset (Fin n)) :
    v T ≤ v S * (1 + ∑ i ∈ T \ S, (c i / B) / (1 - c i / B)) := by
  obtain ⟨hu1, hu2⟩ := CompDesign.thm_5_1_union_bound v hv0 hm hs S T
  have hterm : ∀ i ∈ T \ S, v (insert i S) - v S ≤ v S * ((c i / B) / (1 - c i / B)) := by
    intro i hi
    have := (CompDesign.eq_22_23 v B c hB hv0 hm hs hc hcB S hS hpos i (Finset.mem_sdiff.1 hi).2).2
    rw [mul_comm]; exact this
  have hsum : ∑ i ∈ T \ S, (v (insert i S) - v S) ≤
      v S * ∑ i ∈ T \ S, (c i / B) / (1 - c i / B) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  nlinarith
