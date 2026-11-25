-- Prove2me | solution 1 for Erdos684.eventually_averaging_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:11:27.839238+00:00
-- url     : https://prove2.me/submissions/2d7422fd-0d24-4a3a-bf0f-6909d555cb65

module
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega
public import Definitions.Def_Erdos684_Analytic
public import Theorems.Thm_Erdos684_eventually_upper_parameters

set_option autoImplicit false
@[expose] public section
open Filter Real
open scoped Topology
public section
open Erdos684
namespace Erdos684
theorem _root_.solution :
    ∀ᶠ n : ℕ in atTop,
      4 * (primeCutoff n : ℝ) * log n <
        (windowLength n : ℝ) * (Chebyshev.theta (primeCutoff n) -
          (windowLength n : ℝ) * log ((n + windowLength n : ℕ) : ℝ)) := by
  filter_upwards [eventually_upper_parameters] with n hn
  obtain ⟨hL, _, _, _, ha, hau, hx, hxu, hb, ht, _⟩ := hn
  have hL0 : 0 ≤ log (n : ℝ) := by linarith
  have ha0 : (0 : ℝ) ≤ windowLength n := Nat.cast_nonneg _
  have hab := mul_le_mul_of_nonneg_left hb ha0
  have hab' := mul_le_mul_of_nonneg_right hau (show 0 ≤ 2 * log (n : ℝ) by positivity)
  have hbudget : 62 * (log (n : ℝ)) ^ 2 ≤
      Chebyshev.theta (primeCutoff n) -
        (windowLength n : ℝ) * log ((n + windowLength n : ℕ) : ℝ) := by
    nlinarith
  have hprod := mul_le_mul ha hbudget (by positivity) ha0
  have hXprod := mul_le_mul_of_nonneg_right hxu (show 0 ≤ 4 * log (n : ℝ) by positivity)
  have hcube : 0 < (log (n : ℝ)) ^ 3 := pow_pos (by linarith) _
  nlinarith
end Erdos684
