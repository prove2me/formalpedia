-- Prove2me | solution 1 for Deduction.mellin_Gchi_of_ne_one_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:50:48.030602+00:00
-- url     : https://prove2.me/submissions/f375859f-55e8-429e-9485-798d609a9246

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauZeroFreeCriterion
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_MellinRamp
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_mellinGchiOfNeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Deduction
namespace Deduction
theorem _root_.solution (f : ℕ → ℂ) (y : ℝ) :
    HasSum (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * f n *
      ((max (y / n - 1) 0 : ℝ) : ℂ)) (ramp f y) := by
  unfold ramp
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  have hn' : ⌊y⌋₊ + 1 ≤ n := by simpa using hn
  have hpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hlt : y < n := by
    have h1 := Nat.lt_floor_add_one y
    have h2 : ((⌊y⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn'
    push_cast at h2
    linarith
  have : max (y / n - 1) 0 = 0 := by
    apply max_eq_right
    have := (div_lt_one hpos).mpr hlt
    linarith
  rw [this]
  simp
end Deduction
