-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.quantitativeLowerBound_explicit_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/54c40276-ec64-4e0f-a686-78aaec9554d5

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_one_le_log_nat_of_three_le
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_two_mul_stage_le_paletteColourCount
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_allColourPaletteRamsey_exponential_bound_sharp
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteStage_cube_root_control_six_sharp
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteColourCount_three
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_quantitativeLowerBound_explicit_small

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution :
    ∀ k : ℕ, 2 ≤ k →
      (((1 : ℝ) / (6 * Real.exp 38)) *
        (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
          (triangleRamseyNumber k : ℝ) := by
  intro k hk
  by_cases hlarge : paletteColourCount 3 ≤ k
  · obtain ⟨H, hH, hlower, hupper, hramsey⟩ :=
      allColourPaletteRamsey_exponential_bound_sharp k hlarge
    have hkthree : 3 ≤ k := by
      have hstage := (two_mul_stage_le_paletteColourCount H).trans hlower
      omega
    have hlog : 0 < Real.log (k : ℝ) := by
      have hone := one_le_log_nat_of_three_le k hkthree
      linarith
    have hroot :=
      paletteStage_cube_root_control_six_sharp H k hH hlower hupper
    have hbase :
        ((1 : ℝ) / (6 * Real.exp 38)) *
            (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ) ≤
          (H : ℝ) / Real.exp 38 := by
      calc
        ((1 : ℝ) / (6 * Real.exp 38)) *
            (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ) =
          (k : ℝ) ^ ((1 : ℝ) / 3) /
            (6 * Real.log (k : ℝ) * Real.exp 38) := by
          field_simp
        _ ≤ (H : ℝ) / Real.exp 38 := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          nlinarith [mul_le_mul_of_nonneg_right hroot
            (Real.exp_pos 38).le]
    calc
      (((1 : ℝ) / (6 * Real.exp 38)) *
          (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
        ((H : ℝ) / Real.exp 38) ^ k := by gcongr
      _ ≤ (triangleRamseyNumber k : ℝ) := hramsey
  · apply quantitativeLowerBound_explicit_small k hk
    rw [paletteColourCount_three] at hlarge
    omega
end ErdosProblems.MulticolourTriangleRamsey
