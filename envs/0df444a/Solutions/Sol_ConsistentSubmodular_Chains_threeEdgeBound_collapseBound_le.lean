-- Prove2me | solution 1 for ConsistentSubmodular.Chains.threeEdgeBound_collapseBound_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:49.060651+00:00
-- url     : https://prove2.me/submissions/c831cfe3-3d6d-483c-9441-d0e679142bb6

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains
import Theorems.Thm_ConsistentSubmodular_Chains_psi_root_unique
import Theorems.Thm_ConsistentSubmodular_Chains_qStar_bounds
import Theorems.Thm_ConsistentSubmodular_Chains_twoEdgeRatio_le

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

theorem xiStar_pos : 0 < xiStar := by linarith [xiStar_root.1]

theorem xiStar_lt_one : xiStar < 1 := xiStar_root.2.1

theorem qStar_pos : 0 < qStar := div_pos (by linarith [xiStar_lt_one]) xiStar_pos

end ConsistentSubmodular.Chains

end

end

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular.Chains

/-- **Inequality (15)**: `φ(x, y) + φ(y, 1) ≤ q` for `x ≥ y ≥ 1`. -/
theorem twoEdge_le {x y : ℝ} (hy : 1 ≤ y) (hyx : y ≤ x) :
    edgeValue x y + edgeValue y 1 ≤ qStar := by
  have h := twoEdgeRatio_le hy hyx
  have hD : 0 < x + y - 1 := by linarith
  unfold twoEdgeRatio at h
  rw [div_le_iff₀ hD] at h
  unfold edgeValue
  linarith

theorem one_sub_qStar_pos : 0 < 1 - qStar := by linarith [qStar_bounds.2]

theorem four_thirds_lt_collapseBound : (4 : ℝ) / 3 < collapseBound := by
  rw [collapseBound, lt_div_iff₀ one_sub_qStar_pos]
  linarith [qStar_bounds.1]

end ConsistentSubmodular.Chains

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem solution : threeEdgeBound collapseBound ≤ qStar := by
  have hq := qStar_bounds
  have hq0 := qStar_pos
  have hL := four_thirds_lt_collapseBound
  have hL0 : 0 < collapseBound := by linarith
  have hqL : qStar + 1 / collapseBound = 1 := by
    rw [collapseBound, one_div_one_div]
    ring
  set r := Real.sqrt (qStar * collapseBound) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (mul_pos hq0 hL0)
  have hr2 : r ^ 2 = qStar * collapseBound := Real.sq_sqrt (mul_pos hq0 hL0).le
  -- `x⋆ = r/q = √(L/q)`, and `x⋆ ≥ L` because `q L < 1`.
  have hqL1 : qStar * collapseBound < 1 := by
    rw [collapseBound, mul_one_div, div_lt_one one_sub_qStar_pos]
    linarith
  have hxL : collapseBound ≤ r / qStar := by
    rw [le_div_iff₀ hq0]
    nlinarith
  have h17 := twoEdge_le (x := r / qStar) (y := collapseBound) (by linarith) hxL
  have hval : threeEdgeBound collapseBound = edgeValue (r / qStar) collapseBound +
      edgeValue collapseBound 1 := by
    have hL1 : 1 / collapseBound = 1 - qStar := by
      rw [collapseBound, one_div_one_div]
    have hdiv : collapseBound / (r / qStar) = r := by
      rw [div_div_eq_mul_div, div_eq_iff hr0.ne']
      linear_combination (-1 : ℝ) * hr2
    have hmul : qStar * (r / qStar) = r := by
      field_simp
    rw [threeEdgeBound, hqL, Real.sqrt_one, ← hr]
    unfold edgeValue
    rw [hdiv, hL1, mul_sub, hmul]
    ring
  linarith

end
