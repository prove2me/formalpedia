-- Prove2me | solution 1 for AvramDividend.Classical.chat03_official_upper_grid_clock_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:55:31.587103+00:00
-- url     : https://prove2.me/submissions/2cf3d3a3-9938-4503-974c-f2de1cd604eb

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_finite_extended_infimum_isGLB
import Theorems.Thm_AvramDividend_Classical_chat03_upper_grid_ennreal_bracket
import Theorems.Thm_AvramDividend_Classical_chat03_ennreal_grid_clock_tendsto_of_mesh_brackets
import Theorems.Thm_AvramDividend_Classical_chat03_official_no_upper_exit_grid_inf_top
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-!
Exact uniformly sampled strict upper-passage ENNReal clocks converge to
the named continuous clock, with finite and infinite passages separated.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (upper : ℝ)
    (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto
      (fun n => ⨅ k : ℕ,
        if upper < X.X ((k : ℝ≥0) * mesh n) ω then
          (((k : ℝ≥0) * mesh n) : ℝ≥0∞)
        else ∞)
      atTop (𝓝 (twoSidedExitUpTime X upper ω)) := by
  by_cases hInf : twoSidedExitUpTime X upper ω = ∞
  · have hEq :
        (fun n : ℕ => ⨅ k : ℕ,
          if upper < X.X ((k : ℝ≥0) * mesh n) ω then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞)
          else ∞) = (fun _ : ℕ => (∞ : ℝ≥0∞)) := by
      funext n
      exact chat03_official_no_upper_exit_grid_inf_top
        X ω upper (mesh n) hInf
    rw [hEq, hInf]
    exact tendsto_const_nhds
  · have hGLB : IsGLB {t : ℝ≥0 | upper < X.X t ω}
        (twoSidedExitUpTime X upper ω).toNNReal :=
      chat03_finite_extended_infimum_isGLB
        (fun t : ℝ≥0 => upper < X.X t ω)
        (twoSidedExitUpTime X upper ω) (by rfl) hInf
    have hConv : Tendsto
        (fun n => ⨅ k : ℕ,
          if upper < X.X ((k : ℝ≥0) * mesh n) ω then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞)
          else ∞) atTop
        (𝓝 ((twoSidedExitUpTime X upper ω).toNNReal : ℝ≥0∞)) := by
      apply chat03_ennreal_grid_clock_tendsto_of_mesh_brackets
        (twoSidedExitUpTime X upper ω).toNNReal mesh _ hzero
      intro ε hε
      obtain ⟨δ, hδ, hbracket⟩ :=
        chat03_upper_grid_ennreal_bracket X ω upper
          (twoSidedExitUpTime X upper ω).toNNReal hGLB ε hε
      refine ⟨δ, hδ, ?_⟩
      intro n hn
      exact hbracket (mesh n) (hpos n) hn
    rw [ENNReal.coe_toNNReal hInf] at hConv
    exact hConv
