-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.paletteColourCount_adjacent_scaled_sharp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/17e5f2e9-14a8-4496-8777-ccbf94ffc36c

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_stageWidths_succ_le
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteLogWidth_le_stage
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_saturatedMatrixRows_adjacent_scaled_sharp

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H : ℕ) (hH : 3 ≤ H) :
    paletteLogWidth H * paletteColourCount (H + 1) ≤
      (paletteLogWidth H + 34) * paletteColourCount H := by
  let a := paletteLogWidth H
  let s := saturatedMatrixRows H
  let s' := saturatedMatrixRows (H + 1)
  have haH : a ≤ H := by
    simpa [a] using paletteLogWidth_le_stage H (by omega)
  have ha' : paletteLogWidth (H + 1) ≤ a + 1 := by
    simpa [a] using (stageWidths_succ_le H (by omega)).1
  have hrows : H * s' ≤ (H + 14) * s := by
    simpa [s, s'] using saturatedMatrixRows_adjacent_scaled_sharp H hH
  have hHreal : (3 : ℝ) ≤ H := by exact_mod_cast hH
  have hareal : (a : ℝ) ≤ H := by exact_mod_cast haH
  have hpolyreal :
      ((H : ℝ) + 1) * ((a : ℝ) + 1) * ((H : ℝ) + 14) ≤
        ((a : ℝ) + 34) * (H : ℝ) ^ 2 := by
    nlinarith [
      mul_nonneg (show 0 ≤ 15 * (H : ℝ) + 14 by positivity)
        (sub_nonneg.mpr hareal),
      mul_nonneg (show 0 ≤ (H : ℝ) - 3 by linarith)
        (show 0 ≤ 18 * (H : ℝ) + 25 by positivity)]
  have hpoly :
      (H + 1) * (a + 1) * (H + 14) ≤ (a + 34) * H ^ 2 := by
    exact_mod_cast hpolyreal
  have hstep : (H + 1) * (a + 1) * s' ≤ (a + 34) * H * s := by
    apply Nat.le_of_mul_le_mul_left (c := H) ?_ (by omega)
    calc
      H * ((H + 1) * (a + 1) * s') =
          ((H + 1) * (a + 1)) * (H * s') := by ring
      _ ≤ ((H + 1) * (a + 1)) * ((H + 14) * s) :=
        Nat.mul_le_mul_left _ hrows
      _ = ((H + 1) * (a + 1) * (H + 14)) * s := by ring
      _ ≤ ((a + 34) * H ^ 2) * s :=
        Nat.mul_le_mul_right s hpoly
      _ = H * ((a + 34) * H * s) := by ring
  calc
    paletteLogWidth H * paletteColourCount (H + 1) =
        a * ((H + 1) * paletteLogWidth (H + 1) * s') := by
      simp only [a, s', paletteColourCount]
      ring
    _ ≤ a * ((H + 1) * (a + 1) * s') := by
      gcongr
    _ ≤ a * ((a + 34) * H * s) := Nat.mul_le_mul_left a hstep
    _ = (paletteLogWidth H + 34) * paletteColourCount H := by
      simp only [a, s, paletteColourCount]
      ring
end ErdosProblems.MulticolourTriangleRamsey
