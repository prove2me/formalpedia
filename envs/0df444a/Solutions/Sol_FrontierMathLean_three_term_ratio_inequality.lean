-- Prove2me | solution 1 for FrontierMathLean.three_term_ratio_inequality
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T08:51:47.14485+00:00
-- url     : https://prove2.me/submissions/f4017518-7690-4bee-9ce9-01c714a75a08

import Definitions.Def_FrontierMathLean_AbstractInequality
import Mathlib.Tactic.Ring
import Definitions.Def_FrontierMathLean_ThreeTermInequality
import Theorems.Thm_FrontierMathLean_normalized_three_variable_inequality


set_option autoImplicit false
open FrontierMathLean
namespace FrontierMathLean
theorem _root_.solution
    {A B C r : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hr : 1 ≤ r) (hrB : r ≤ B / A) (hrC : r ≤ C / A) :
    5 + 2 * (r + r⁻¹) ≤
      (A + B + C) * (A⁻¹ + B⁻¹ + C⁻¹) := by
  have hnormalized := normalized_three_variable_inequality hr hrB hrC
  calc
    5 + 2 * (r + r⁻¹) ≤
        3 + (B / A + (B / A)⁻¹) + (C / A + (C / A)⁻¹) +
          ((B / A) / (C / A) + (C / A) / (B / A)) := hnormalized
    _ = (A + B + C) * (A⁻¹ + B⁻¹ + C⁻¹) := by
      field_simp [hA.ne', hB.ne', hC.ne']
      ring
end FrontierMathLean
