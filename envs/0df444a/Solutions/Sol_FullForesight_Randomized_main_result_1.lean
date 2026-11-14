-- Prove2me | solution 1 for FullForesight.Randomized.main_result_1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:07:08.735087+00:00
-- url     : https://prove2.me/submissions/5cdfa25f-9a3c-4118-9ca3-0d78d6db6668

import Mathlib
import Definitions.Def_FullForesight_Randomized_Constants
import Definitions.Def_FullForesight_Randomized_Model
import Definitions.Def_FullForesight_Randomized_Coverage
import Theorems.Thm_FullForesight_Randomized_proposition_1
import Theorems.Thm_FullForesight_Randomized_theorem_2
import Theorems.Thm_FullForesight_Randomized_remark_1

open FullForesight.Randomized in
theorem solution :
    ((1 / 2 : ℝ) < xiStar ∧ xiStar < 1 ∧ Psi xiStar = 0 ∧
        (∀ ξ ∈ Set.Ioo (1 / 2 : ℝ) 1, Psi ξ = 0 → ξ = xiStar) ∧
        |xiStar - 0.7942| < 0.00005) ∧
      (∃ c : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∀ (n k : ℕ) (f : Finset (Fin n) → ℝ), IsInstance k f →
          ∃ L : TrajLaw n, L.Valid k ∧ L.Consistent (c / ε ^ 2) ∧
            L.Approx f k (xiStar - ε)) ∧
      (∀ C α : ℝ, xiStar < α →
        ∃ (n k : ℕ) (s : Fin n → Finset ℕ), 1 ≤ k ∧
          ∀ L : TrajLaw n, L.Valid k → L.Consistent C → ¬ L.Approx (coverage s) k α) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := proposition_1
  refine ⟨⟨h1, h2, h3, h4, ?_⟩, theorem_2, ?_⟩
  · rw [abs_lt]
    constructor <;> norm_num <;> linarith
  · intro C α hα
    obtain ⟨K, hK⟩ := remark_1 C ((α - xiStar) / 2) (by linarith)
    obtain ⟨n, s, hs⟩ := hK (max K 1) (le_max_left _ _)
    exact ⟨n, max K 1, s, le_max_right _ _, fun L hv hc => hs L hv hc α (by linarith)⟩
