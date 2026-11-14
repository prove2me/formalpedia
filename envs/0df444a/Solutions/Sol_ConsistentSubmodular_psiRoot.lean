-- Prove2me | solution 1 for ConsistentSubmodular.psiRoot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:34.456214+00:00
-- url     : https://prove2.me/submissions/e674a551-7e31-41de-bd18-37dde6fc5479

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements
import Theorems.Thm_ConsistentSubmodular_Chains_psi_root_unique

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

theorem continuous_psi : Continuous psi := by
  unfold psi
  fun_prop

/-- Existence in Proposition 1: `Ψ(1/2) = -83/16 < 0 < 24 = Ψ(1)`, so the
intermediate value theorem gives a root in `(1/2, 1)`. -/
theorem exists_psi_root : ∃ ξ : ℝ, 1 / 2 < ξ ∧ ξ < 1 ∧ psi ξ = 0 := by
  have hsub := intermediate_value_Ioo (show (1 / 2 : ℝ) ≤ 1 by norm_num)
    continuous_psi.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (psi (1 / 2)) (psi 1) := by
    constructor <;> norm_num [psi]
  obtain ⟨ξ, ⟨h1, h2⟩, hξ⟩ := hsub hmem
  exact ⟨ξ, h1, h2, hξ⟩

/-- The root of `Ψ` in `(1/2, 1)` is `ξ⋆`. -/
theorem eq_xiStar {ξ : ℝ} (h₁ : 1 / 2 < ξ) (h₂ : ξ < 1) (hψ : psi ξ = 0) : ξ = xiStar := by
  have hset : {ξ : ℝ | 1 / 2 < ξ ∧ ξ < 1 ∧ psi ξ = 0} = {ξ} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx₁, hx₂, hx⟩
      exact psi_root_unique hx₁ hx₂ h₁ h₂ hx hψ
    · rintro rfl
      exact ⟨h₁, h₂, hψ⟩
  rw [xiStar, hset, csSup_singleton]

/-- `ξ⋆` is the root of `Ψ` in `(1/2, 1)`. -/
theorem xiStar_root : 1 / 2 < xiStar ∧ xiStar < 1 ∧ psi xiStar = 0 := by
  obtain ⟨ξ, h1, h2, hψ⟩ := exists_psi_root
  have h := eq_xiStar h1 h2 hψ
  subst h
  exact ⟨h1, h2, hψ⟩

/-- The numerical value in Proposition 1: `Ψ(0.7941970146) < 0 < Ψ(0.7941970148)`,
so `Ψ` has a root between these points, and it is `ξ⋆` by uniqueness. -/
theorem xiStar_bounds : (0.7941970146 : ℝ) < xiStar ∧ xiStar < 0.7941970148 := by
  have hsub := intermediate_value_Ioo (show (0.7941970146 : ℝ) ≤ 0.7941970148 by norm_num)
    continuous_psi.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Ioo (psi 0.7941970146) (psi 0.7941970148) := by
    constructor <;> norm_num [psi]
  obtain ⟨ξ, ⟨h1, h2⟩, hψ⟩ := hsub hmem
  have h := eq_xiStar (by linarith) (by linarith) hψ
  subst h
  exact ⟨h1, h2⟩

/-- **Proposition 1**: `Ψ` has a unique root `ξ⋆ ∈ (1/2, 1)`, and
`0.7941970146 < ξ⋆ < 0.7941970148`. -/
theorem psiRoot : PsiRootGoal := by
  obtain ⟨h1, h2, hψ⟩ := xiStar_root
  obtain ⟨b1, b2⟩ := xiStar_bounds
  exact ⟨h1, h2, hψ, fun ξ hξ₁ hξ₂ hψξ => eq_xiStar hξ₁ hξ₂ hψξ, b1, b2⟩

end ConsistentSubmodular.Chains

end

end

section

open ConsistentSubmodular

theorem solution : PsiRootGoal :=
  Chains.psiRoot

end
