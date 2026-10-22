-- Prove2me | solution 1 for BirkhoffGlobalSection.left_component_position_coordinates_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-23T18:38:05.672398+00:00
-- url     : https://prove2.me/submissions/878483ed-412a-4c48-af15-049f2419815d

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Real.Sqrt
import Theorems.Thm_BirkhoffGlobalSection_left_component_jacobi_position_radius_bounded

open BirkhoffGlobalSection

theorem solution (μ c : ℝ)
    (hμ0 : 0 < μ) (hμ1 : μ < 1)
    (hc : belowFirstCriticalValue μ c) :
    ∃ Rz : ℝ, ∀ s ∈ leftEnergyComponent μ c,
      |s 0| ≤ Rz ∧ |s 1| ≤ Rz := by
  obtain ⟨Rq, hq⟩ :=
    left_component_jacobi_position_radius_bounded μ c hμ0 hμ1 hc
  refine ⟨Real.sqrt (max 1 Rq), ?_⟩
  intro s hs
  have hid : ((leviCivitaPosition μ s) 0 + μ) ^ 2 +
      ((leviCivitaPosition μ s) 1) ^ 2 =
        4 * (zNormSq s) ^ 2 := by
    simp [leviCivitaPosition, zNormSq]
    ring
  have hrad : 4 * (zNormSq s) ^ 2 ≤ Rq := by
    simpa only [hid] using hq s hs
  have hznonneg : 0 ≤ zNormSq s := by
    unfold zNormSq
    positivity
  have hzbound : zNormSq s ≤ max 1 Rq := by
    by_cases hsmall : zNormSq s ≤ 1
    · exact hsmall.trans (le_max_left 1 Rq)
    · have hone : 1 ≤ zNormSq s := le_of_not_ge hsmall
      have hsq : zNormSq s ≤ (zNormSq s) ^ 2 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hone) hznonneg]
      nlinarith [le_max_right (1 : ℝ) Rq]
  have hx : (s 0) ^ 2 ≤ max 1 Rq := by
    dsimp [zNormSq] at hzbound
    nlinarith [sq_nonneg (s 1)]
  have hy : (s 1) ^ 2 ≤ max 1 Rq := by
    dsimp [zNormSq] at hzbound
    nlinarith [sq_nonneg (s 0)]
  exact ⟨Real.abs_le_sqrt hx, Real.abs_le_sqrt hy⟩
