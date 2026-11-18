-- Prove2me | solution 1 for CompDesignBFM.large_market_submodular_poa
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T04:45:23.465031+00:00
-- url     : https://prove2.me/submissions/dcd5faa9-88da-4b6b-b52d-440d0d3f3d82

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_kappa
import Theorems.Thm_CompDesign_theorem_4_1
import Theorems.Thm_CompDesign_theorem_5_1

open CompDesignBFM

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ i, 0 ≤ c i)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1) (hcl : ∀ i, c i ≤ l * B) :
    (∃ S : Finset (Fin n), IsPNE v B c S) ∧
      ∀ S : Finset (Fin n), IsPNE v B c S → OPT v B c ≤ (1 + 1 / (1 - l)) * v S := by
  have hcB : ∀ i, c i < B := fun i => by nlinarith [hcl i]
  refine ⟨(CompDesign.theorem_4_1 v B c hB hv0 hm hs hc hcB).2, ?_⟩
  intro S hS
  have hnn : 0 ≤ v S := hv0 ▸ hm ∅ S (Finset.empty_subset S)
  obtain ⟨h1, h2⟩ := CompDesign.theorem_5_1 v B c hB hv0 hm hs hc l hl0 hl1 hcl
  have hl' : 0 < 1 - l := by linarith
  have e : (2 - l) / (1 - l) = 1 + 1 / (1 - l) := by field_simp; ring
  calc OPT v B c ≤ (1 + CompDesign.kappa l) * v S := h1 S hS
    _ ≤ (1 + 1 / (1 - l)) * v S := by
        apply mul_le_mul_of_nonneg_right _ hnn
        rw [← e]; exact h2
