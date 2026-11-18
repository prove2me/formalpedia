-- Prove2me | solution 1 for CompDesign.main_result_2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T05:12:20.134823+00:00
-- url     : https://prove2.me/submissions/2f92c66a-b5d8-44f8-baab-a99e6b4187bc

import Mathlib
import Definitions.Def_CompDesignBFM_IsMonotoneSF
import Definitions.Def_CompDesignBFM_IsSubmodularSF
import Definitions.Def_CompDesignBFM_IsPNE
import Definitions.Def_CompDesignBFM_OPT
import Definitions.Def_CompDesign_IsStrictImprovement
import Definitions.Def_CompDesign_kappa
import Theorems.Thm_CompDesign_theorem_4_1
import Theorems.Thm_CompDesign_theorem_5_1

open CompDesignBFM

theorem solution {n : ℕ} (v : Finset (Fin n) → ℝ) (B : ℝ) (c : Fin n → ℝ) (hB : 0 < B)
    (hv0 : v ∅ = 0) (hm : IsMonotoneSF v) (hs : IsSubmodularSF v) (hc : ∀ i, 0 ≤ c i)
    (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1) (hcl : ∀ i, c i ≤ l * B) :
    (¬ ∃ f : ℕ → Finset (Fin n), ∀ t, CompDesign.IsStrictImprovement v B c (f t) (f (t + 1))) ∧
    (∃ S : Finset (Fin n), IsPNE v B c S) ∧
    (∀ S : Finset (Fin n), IsPNE v B c S → OPT v B c ≤ (1 + CompDesign.kappa l) * v S) ∧
    1 + CompDesign.kappa l ≤ (2 - l) / (1 - l) := by
  have hcB : ∀ i, c i < B := fun i => by nlinarith [hcl i]
  obtain ⟨h1, h2⟩ := CompDesign.theorem_4_1 v B c hB hv0 hm hs hc hcB
  obtain ⟨h3, h4⟩ := CompDesign.theorem_5_1 v B c hB hv0 hm hs hc l hl0 hl1 hcl
  exact ⟨h1, h2, h3, h4⟩
