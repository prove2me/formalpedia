-- Prove2me | solution 1 for AvramDividend.Classical.chat03_official_lower_grid_clock_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:55:28.638991+00:00
-- url     : https://prove2.me/submissions/40055894-be6d-4be1-8647-8a539ab13b32

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_finite_extended_infimum_isGLB
import Theorems.Thm_AvramDividend_Classical_chat03_lower_grid_ennreal_bracket
import Theorems.Thm_AvramDividend_Classical_chat03_ennreal_grid_clock_tendsto_of_mesh_brackets
import Theorems.Thm_AvramDividend_Classical_chat03_official_no_lower_exit_grid_inf_top
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-!
Exact uniformly sampled strict lower-passage ENNReal clocks converge to
the named continuous clock, with finite and infinite passages separated.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower : ℝ)
    (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto
      (fun n => ⨅ k : ℕ,
        if X.X ((k : ℝ≥0) * mesh n) ω < lower then
          (((k : ℝ≥0) * mesh n) : ℝ≥0∞)
        else ∞)
      atTop (𝓝 (twoSidedExitDownTime X lower ω)) := by
  by_cases hInf : twoSidedExitDownTime X lower ω = ∞
  · have hEq :
        (fun n : ℕ => ⨅ k : ℕ,
          if X.X ((k : ℝ≥0) * mesh n) ω < lower then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞)
          else ∞) = (fun _ : ℕ => (∞ : ℝ≥0∞)) := by
      funext n
      exact chat03_official_no_lower_exit_grid_inf_top
        X ω lower (mesh n) hInf
    rw [hEq, hInf]
    exact tendsto_const_nhds
  · have hGLB : IsGLB {t : ℝ≥0 | X.X t ω < lower}
        (twoSidedExitDownTime X lower ω).toNNReal :=
      chat03_finite_extended_infimum_isGLB
        (fun t : ℝ≥0 => X.X t ω < lower)
        (twoSidedExitDownTime X lower ω) (by rfl) hInf
    have hConv : Tendsto
        (fun n => ⨅ k : ℕ,
          if X.X ((k : ℝ≥0) * mesh n) ω < lower then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞)
          else ∞) atTop
        (𝓝 ((twoSidedExitDownTime X lower ω).toNNReal : ℝ≥0∞)) := by
      apply chat03_ennreal_grid_clock_tendsto_of_mesh_brackets
        (twoSidedExitDownTime X lower ω).toNNReal mesh _ hzero
      intro ε hε
      obtain ⟨δ, hδ, hbracket⟩ :=
        chat03_lower_grid_ennreal_bracket X ω lower
          (twoSidedExitDownTime X lower ω).toNNReal hGLB ε hε
      refine ⟨δ, hδ, ?_⟩
      intro n hn
      exact hbracket (mesh n) (hpos n) hn
    rw [ENNReal.coe_toNNReal hInf] at hConv
    exact hConv
