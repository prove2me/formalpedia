-- Prove2me | solution 1 for ConsistentSubmodular.Chains.threeEdge_le_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:53.281291+00:00
-- url     : https://prove2.me/submissions/58b75858-2bb2-48d7-88a2-6531e649772d

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains
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

/-- The arithmetic–geometric mean inequality `a x + b/x ≥ 2 √(a b)`. -/
theorem two_sqrt_le {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 < x) :
    2 * Real.sqrt (a * b) ≤ a * x + b / x := by
  have h1 : Real.sqrt (a * x) ^ 2 = a * x := Real.sq_sqrt (by positivity)
  have h2 : Real.sqrt (b / x) ^ 2 = b / x := Real.sq_sqrt (by positivity)
  have h3 : Real.sqrt (a * x) * Real.sqrt (b / x) = Real.sqrt (a * b) := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  nlinarith [sq_nonneg (Real.sqrt (a * x) - Real.sqrt (b / x))]

end ConsistentSubmodular.Chains

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem solution {x y z : ℝ} (hz : 1 ≤ z) (hzy : z ≤ y) (hyx : y ≤ x) :
    edgeValue x y + edgeValue y z + edgeValue z 1 ≤ threeEdgeBound y := by
  have hq := qStar_pos
  have hy0 : 0 < y := by linarith
  have hx0 : 0 < x := by linarith
  have hz0 : 0 < z := by linarith
  have hid : edgeValue x y + edgeValue y z + edgeValue z 1 =
      3 + 3 * qStar - qStar * y - (qStar * x + y / x) - ((qStar + 1 / y) * z + 1 / z) := by
    unfold edgeValue
    field_simp
    ring
  have h1 := two_sqrt_le hq.le hy0.le hx0
  have h2 := two_sqrt_le (a := qStar + 1 / y) (b := 1) (by positivity) zero_le_one hz0
  rw [mul_one] at h2
  rw [hid, threeEdgeBound]
  linarith

end
