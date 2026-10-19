-- Prove2me | solution 1 for ErdosProblems.MulticolourTriangleRamsey.stageWidths_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.335123+00:00
-- url     : https://prove2.me/submissions/a82fa6b1-d459-432a-831c-786c4553393d

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
import Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_log_le_paletteLogWidth

set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology
namespace ErdosProblems.MulticolourTriangleRamsey
theorem _root_.solution (H : ℕ) (hH : 1 ≤ H) :
    paletteLogWidth (H + 1) ≤ paletteLogWidth H + 1 ∧
      saturatedMatrixWidth (H + 1) ≤
        saturatedMatrixWidth H + 2 * paletteLogWidth H + 4 := by
  have hpos : (0 : ℝ) < H := by
    exact_mod_cast (by omega : 0 < H)
  have hHreal : (1 : ℝ) ≤ H := by
    exact_mod_cast hH
  have hinv : 1 / (H : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hpos).mpr
    simpa using hHreal
  have hlogsucc :
      Real.log ((H + 1 : ℕ) : ℝ) ≤
        Real.log (H : ℝ) + 1 / (H : ℝ) := by
    have hsucc : (0 : ℝ) < ((H + 1 : ℕ) : ℝ) := by positivity
    have hbound := Real.log_le_sub_one_of_pos (div_pos hsucc hpos)
    rw [Real.log_div hsucc.ne' hpos.ne'] at hbound
    have hratio :
        ((H + 1 : ℕ) : ℝ) / (H : ℝ) - 1 = 1 / (H : ℝ) := by
      push_cast
      field_simp
      ring
    rw [hratio] at hbound
    linarith
  constructor
  · have hceil :
        ⌈Real.log ((H + 1 : ℕ) : ℝ)⌉₊ ≤
          ⌈Real.log (H : ℝ)⌉₊ + 1 := by
      apply Nat.ceil_le.mpr
      push_cast
      have hlogsucc_real :
          Real.log ((H : ℝ) + 1) ≤
            Real.log (H : ℝ) + 1 / (H : ℝ) := by
        simpa using hlogsucc
      linarith [Nat.le_ceil (Real.log (H : ℝ))]
    change
      max 2 ⌈Real.log ((H + 1 : ℕ) : ℝ)⌉₊ ≤
        max 2 ⌈Real.log (H : ℝ)⌉₊ + 1
    exact max_le (by omega)
      (hceil.trans (Nat.add_le_add_right
        (Nat.le_max_right 2 ⌈Real.log (H : ℝ)⌉₊) 1))
  · have htwoinv : 2 / (H : ℝ) ≤ 2 := by
      calc
        2 / (H : ℝ) = 2 * (1 / (H : ℝ)) := by ring
        _ ≤ 2 * 1 := by gcongr
        _ = 2 := by norm_num
    have hprevious :
        2 * (H : ℝ) * Real.log (H : ℝ) ≤
          (saturatedMatrixWidth H : ℝ) := Nat.le_ceil _
    change
      ⌈2 * (((H + 1 : ℕ) : ℝ)) *
        Real.log ((H + 1 : ℕ) : ℝ)⌉₊ ≤
          saturatedMatrixWidth H + 2 * paletteLogWidth H + 4
    apply Nat.ceil_le.mpr
    push_cast
    calc
      2 * ((H : ℝ) + 1) * Real.log ((H : ℝ) + 1) ≤
        2 * ((H : ℝ) + 1) *
          (Real.log (H : ℝ) + 1 / (H : ℝ)) := by
            gcongr
            simpa using hlogsucc
      _ = 2 * (H : ℝ) * Real.log (H : ℝ) +
          2 * Real.log (H : ℝ) + 2 + 2 / (H : ℝ) := by
            field_simp
            ring
      _ ≤ (saturatedMatrixWidth H : ℝ) +
          2 * (paletteLogWidth H : ℝ) + 4 := by
            linarith [log_le_paletteLogWidth H]
end ErdosProblems.MulticolourTriangleRamsey
