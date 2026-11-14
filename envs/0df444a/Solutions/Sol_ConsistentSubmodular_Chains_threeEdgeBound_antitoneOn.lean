-- Prove2me | solution 1 for ConsistentSubmodular.Chains.threeEdgeBound_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:59.872245+00:00
-- url     : https://prove2.me/submissions/67f0c73c-e516-4359-a63c-d1d50ee38795

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_ConsecutiveChains
import Theorems.Thm_ConsistentSubmodular_Chains_psi_root_unique
import Theorems.Thm_ConsistentSubmodular_Chains_qStar_bounds

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

theorem one_sub_qStar_pos : 0 < 1 - qStar := by linarith [qStar_bounds.2]

theorem four_thirds_lt_collapseBound : (4 : ℝ) / 3 < collapseBound := by
  rw [collapseBound, lt_div_iff₀ one_sub_qStar_pos]
  linarith [qStar_bounds.1]

theorem hasDerivAt_threeEdgeBound {y : ℝ} (hy : 0 < y) :
    HasDerivAt threeEdgeBound
      (-qStar - qStar / Real.sqrt (qStar * y) + 1 / (y ^ 2 * Real.sqrt (qStar + 1 / y))) y := by
  have hq := qStar_pos
  have hqy : qStar * y ≠ 0 := (mul_pos hq hy).ne'
  have hqy' : qStar + 1 / y ≠ 0 := by positivity
  have h1 : HasDerivAt (fun t => Real.sqrt (qStar * t)) (qStar / (2 * Real.sqrt (qStar * y))) y := by
    have := ((hasDerivAt_id y).const_mul qStar).sqrt (by simpa using hqy)
    simpa using this
  have h2 : HasDerivAt (fun t => Real.sqrt (qStar + 1 / t))
      (-(1 / y ^ 2) / (2 * Real.sqrt (qStar + 1 / y))) y := by
    have hinv : HasDerivAt (fun t => qStar + 1 / t) (-(1 / y ^ 2)) y := by
      have := (hasDerivAt_inv hy.ne').const_add qStar
      simpa [one_div] using this
    exact hinv.sqrt hqy'
  have h := ((((hasDerivAt_const y (3 + 3 * qStar)).sub ((hasDerivAt_id y).const_mul qStar)).sub
    (h1.const_mul 2)).sub (h2.const_mul 2))
  refine h.congr_deriv ?_
  have hs1 : 0 < Real.sqrt (qStar * y) := Real.sqrt_pos.mpr (mul_pos hq hy)
  have hs2 : 0 < Real.sqrt (qStar + 1 / y) := Real.sqrt_pos.mpr (by positivity)
  field_simp
  ring

end ConsistentSubmodular.Chains

end

end

section

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Chains

theorem solution : AntitoneOn threeEdgeBound (Set.Ici collapseBound) := by
  have hq := qStar_bounds
  have hL := four_thirds_lt_collapseBound
  have hderiv : ∀ y ∈ Set.Ici collapseBound, HasDerivAt threeEdgeBound
      (-qStar - qStar / Real.sqrt (qStar * y) + 1 / (y ^ 2 * Real.sqrt (qStar + 1 / y))) y :=
    fun y hy => hasDerivAt_threeEdgeBound (by linarith [Set.mem_Ici.mp hy])
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact fun y hy => (hderiv y hy).continuousAt.continuousWithinAt
  · rw [interior_Ici]
    exact fun y hy => (hderiv y (Set.mem_Ici.mpr (Set.mem_Ioi.mp hy).le)).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro y hy
    have hyL : collapseBound < y := hy
    have hy0 : 0 < y := by linarith
    rw [(hderiv y (Set.mem_Ici.mpr hyL.le)).deriv]
    set w := Real.sqrt y with hw
    have hw0 : 0 < w := Real.sqrt_pos.mpr hy0
    have hw2 : w ^ 2 = y := Real.sq_sqrt hy0.le
    have hsq : Real.sqrt (qStar * y) = Real.sqrt qStar * w := Real.sqrt_mul qStar_pos.le y
    have hsq0 : 1 / 2 < Real.sqrt qStar := by
      rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
        rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    have hs : 1 / w ≤ Real.sqrt (qStar + 1 / y) := by
      apply Real.le_sqrt_of_sq_le
      rw [div_pow, one_pow, hw2]
      linarith [qStar_pos]
    have hs0 : 0 < Real.sqrt (qStar + 1 / y) := lt_of_lt_of_le (by positivity) hs
    -- `1 / (y² s) ≤ 1 / w³`
    have hterm : 1 / (y ^ 2 * Real.sqrt (qStar + 1 / y)) ≤ 1 / w ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
      have : w ^ 3 = y ^ 2 * (1 / w) := by
        rw [← hw2]
        field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    have hw43 : 4 / 3 < w ^ 2 := by linarith
    have hw1 : 23 / 20 < w := by nlinarith
    have hw3 : 23 / 15 < w ^ 3 := by
      have : w ^ 3 = w * w ^ 2 := by ring
      rw [this]
      nlinarith
    have hqw3 : 259 / 1000 * (23 / 15) < qStar * w ^ 3 :=
      mul_lt_mul'' hq.1 hw3 (by norm_num) (by norm_num)
    have hsqw2 : 1 / 2 * (4 / 3) < Real.sqrt qStar * w ^ 2 :=
      mul_lt_mul'' hsq0 hw43 (by norm_num) (by norm_num)
    have hkey : 1 ≤ qStar * w ^ 3 + Real.sqrt qStar * w ^ 2 := by linarith
    have hfrac : 1 / w ^ 3 ≤ qStar + qStar / (Real.sqrt qStar * w) := by
      have hsqpos : 0 < Real.sqrt qStar := Real.sqrt_pos.mpr qStar_pos
      rw [div_le_iff₀ (by positivity)]
      have hsimp : (qStar + qStar / (Real.sqrt qStar * w)) * w ^ 3 =
          qStar * w ^ 3 + qStar / Real.sqrt qStar * w ^ 2 := by
        field_simp
      rw [hsimp, Real.div_sqrt]
      exact hkey
    rw [hsq]
    linarith

end
