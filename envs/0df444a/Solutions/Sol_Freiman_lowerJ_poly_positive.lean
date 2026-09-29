-- Prove2me | solution 1 for Freiman.lowerJ_poly_positive
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:18:02.245859+00:00
-- url     : https://prove2.me/submissions/ca9a5de3-1605-42d5-8ce3-9f644e8ace9a

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

import Theorems.Thm_Freiman_lowerJ_poly_checks
import Theorems.Thm_Freiman_lowerJ_rectangle
import Theorems.Thm_Freiman_lowerJ_denominators
import Theorems.Thm_Freiman_cert_field_lower_bound
import Theorems.Thm_Freiman_cert_bernstein_positive
import Theorems.Thm_Freiman_cert_bernstein_reconstruction
import Theorems.Thm_Freiman_cert_cross_polynomial
import Theorems.Thm_Freiman_cert_threshold_cross_order

open Freiman

theorem solution (i : Fin 4) (r s : ℝ) (hr : r ∈ Set.Icc (1/4:ℝ) (4/5)) (hs : s ∈ Set.Icc (1/4:ℝ) (4/5)) : 0 < lowerJPolyDifference i r s := by
  have hc := Freiman.lowerJ_poly_checks i
  have hm : certRectangleMem lowerJRectangle r s := by
    simpa [certRectangleMem,lowerJRectangle] using (show (1/4:ℝ) ≤ r ∧ r ≤ (4/5:ℝ) ∧ (1/4:ℝ) ≤ s ∧ s ≤ (4/5:ℝ) from ⟨hr.1,hr.2,hs.1,hs.2⟩)
  have hp := Freiman.cert_bernstein_positive (lowerJPolyCoefficients i) lowerJRectangle r s Freiman.lowerJ_rectangle hm (by
    intro a b
    have hl := Freiman.cert_field_lower_bound (lowerJPolyCoefficients i a b)
    have hq : (0:ℝ) < (certFieldLower (lowerJPolyCoefficients i a b):ℝ) := by exact_mod_cast hc.2 a b
    exact lt_of_lt_of_le hq hl)
  rw [hc.1] at hp
  rw [← Freiman.cert_bernstein_reconstruction _ _ Freiman.lowerJ_rectangle] at hp
  rw [Freiman.cert_cross_polynomial] at hp
  have hd := Freiman.lowerJ_denominators i r s hr hs
  exact sub_pos.mpr ((Freiman.cert_threshold_cross_order _ _ r s hd.1 hd.2).2.mp hp)
