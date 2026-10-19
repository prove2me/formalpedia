-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.paletteStage_cube_root_control_six_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/52b6e99b-e9d9-4db9-8d61-c8b3b4fd00db

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_one_le_log_nat_of_three_le
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_two_mul_stage_le_paletteColourCount
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteColourCount_le_twenty_six_sharp

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H k : ℕ)
    (hH : 3 ≤ H)
    (hlower : paletteColourCount H ≤ k)
    (hupper : k < paletteColourCount (H + 1)) :
    (k : ℝ) ^ ((1 : ℝ) / 3) ≤
      6 * (H : ℝ) * Real.log (k : ℝ) := by
  have hkstage : 2 * H ≤ k :=
    (two_mul_stage_le_paletteColourCount H).trans hlower
  have hHk : H + 1 ≤ k := by omega
  have hkthree : 3 ≤ k := by omega
  have hlogk : 1 ≤ Real.log (k : ℝ) :=
    one_le_log_nat_of_three_le k hkthree
  have hlognext :
      Real.log ((H + 1 : ℕ) : ℝ) ≤ Real.log (k : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hHk
  have hHnext : ((H + 1 : ℕ) : ℝ) ≤ 2 * (H : ℝ) := by
    exact_mod_cast (show H + 1 ≤ 2 * H by omega)
  have hkbound :
      (k : ℝ) ≤
        26 * (((H + 1 : ℕ) : ℝ)) ^ 3 *
          Real.log ((H + 1 : ℕ) : ℝ) ^ 3 := by
    calc
      (k : ℝ) ≤ (paletteColourCount (H + 1) : ℝ) := by
        exact_mod_cast (Nat.le_of_lt hupper)
      _ ≤ 26 * (((H + 1 : ℕ) : ℝ)) ^ 3 *
          Real.log ((H + 1 : ℕ) : ℝ) ^ 3 :=
        paletteColourCount_le_twenty_six_sharp (H + 1) (by omega)
  have hcube :
      (k : ℝ) ≤ (6 * (H : ℝ) * Real.log (k : ℝ)) ^ 3 := by
    calc
      (k : ℝ) ≤
          26 * (((H + 1 : ℕ) : ℝ)) ^ 3 *
            Real.log ((H + 1 : ℕ) : ℝ) ^ 3 := hkbound
      _ ≤ 26 * (2 * (H : ℝ)) ^ 3 * Real.log (k : ℝ) ^ 3 := by
        gcongr
      _ = 208 * (H : ℝ) ^ 3 * Real.log (k : ℝ) ^ 3 := by
        ring
      _ ≤ 216 * (H : ℝ) ^ 3 * Real.log (k : ℝ) ^ 3 := by
        gcongr
        norm_num
      _ = (6 * (H : ℝ) * Real.log (k : ℝ)) ^ 3 := by
        ring
  have hrootcube :
      ((k : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) = (k : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  apply (pow_le_pow_iff_left₀
    (Real.rpow_nonneg (by positivity) _)
    (by positivity)
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [hrootcube]
  exact hcube
end ErdosProblems.MulticolourTriangleRamsey
