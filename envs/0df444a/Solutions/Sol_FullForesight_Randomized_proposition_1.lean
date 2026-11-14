-- Prove2me | solution 1 for FullForesight.Randomized.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:51:52.179452+00:00
-- url     : https://prove2.me/submissions/cf547438-6f68-4e5a-b1bb-f936887acde9

import Mathlib
import Definitions.Def_FullForesight_Randomized_Constants
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_psiRoot

namespace FullForesight.Randomized

/-- The two encodings of `Ψ` agree. -/
theorem Psi_eq_psi (ξ : ℝ) : Psi ξ = ConsistentSubmodular.psi ξ := rfl

/-- The two encodings of `ξ⋆` agree: `Ψ` has no root at the endpoints `1/2` and `1`,
so the root set on `[1/2, 1]` is the root set on `(1/2, 1)`. -/
theorem xiStar_eq : xiStar = ConsistentSubmodular.xiStar := by
  unfold xiStar ConsistentSubmodular.xiStar
  congr 1
  ext ξ
  simp only [Set.mem_setOf_eq, Set.mem_Icc, Psi_eq_psi]
  constructor
  · rintro ⟨⟨h1, h2⟩, h0⟩
    refine ⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_, h0⟩
    · rintro rfl
      norm_num [ConsistentSubmodular.psi] at h0
    · rintro rfl
      norm_num [ConsistentSubmodular.psi] at h0
  · rintro ⟨h1, h2, h0⟩
    exact ⟨⟨h1.le, h2.le⟩, h0⟩

end FullForesight.Randomized

open FullForesight.Randomized in
theorem solution :
    (1 / 2 : ℝ) < xiStar ∧ xiStar < 1 ∧ Psi xiStar = 0 ∧
      (∀ ξ ∈ Set.Ioo (1 / 2 : ℝ) 1, Psi ξ = 0 → ξ = xiStar) ∧
      (0.7941970146 : ℝ) < xiStar ∧ xiStar < 0.7941970148 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := ConsistentSubmodular.psiRoot
  rw [xiStar_eq]
  exact ⟨h1, h2, h3, fun ξ hξ h => h4 ξ hξ.1 hξ.2 h, h5, h6⟩
