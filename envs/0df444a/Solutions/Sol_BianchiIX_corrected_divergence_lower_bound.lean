-- Prove2me | solution 1 for BianchiIX.corrected_divergence_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:47:12.793371+00:00
-- url     : https://prove2.me/submissions/d689491d-707d-4904-95d6-35f63dfc3a4d

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Algebra_Flux
import Theorems.Thm_BianchiIX_curvature_lower_bound
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp

open BianchiIX
noncomputable section


theorem solution
    {a b c r : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hr : r ^ 3 = a * b * c) :
    0 < 2 * r ^ 2 / (1 + 4 * r ^ 2) ∧
      2 * r ^ 2 / (1 + 4 * r ^ 2) ≤ correctedDivergence (curvature a b c) (r ^ 2) := by
  have hrne : r ≠ 0 := by
    intro hz
    have hp := mul_pos (mul_pos ha hb) hc
    rw [hz] at hr
    nlinarith only [hr, hp]
  have hrpos : 0 < r ^ 2 := sq_pos_of_ne_zero hrne
  have hden : 0 < 1 + 4 * r ^ 2 := by positivity
  constructor
  · exact div_pos (mul_pos (by norm_num) hrpos) hden
  · unfold correctedDivergence
    apply (div_le_div_iff_of_pos_right hden).mpr
    have := curvature_lower_bound ha hb hc hr
    linarith
