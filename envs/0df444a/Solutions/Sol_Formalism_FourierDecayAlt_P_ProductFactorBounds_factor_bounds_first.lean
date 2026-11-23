-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ProductFactorBounds.factor_bounds_first
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:11.154685+00:00
-- url     : https://prove2.me/submissions/25a6dc2d-43f4-4ed4-aeed-752636798639

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ProductFactorBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ProductFactorBounds
open Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.ProductFactorBounds
theorem _root_.solution (N : ℝ) (hN : 2 ≤ N) (l : WLetter ℝ) (Y : ℝ)
    (h : N ^ 2 ≤ |Y - l.pt|) (hf : l.first = true) :
    1 - 1 / (N ^ 2 - 1) ^ 2 ≤ wFactor l Y ∧ wFactor l Y ≤ 1 + 0 := by
  obtain ⟨p, t, f⟩ := l
  have hN2 : 4 ≤ N ^ 2 := by nlinarith
  have hpos : 0 < N ^ 2 - 1 := by linarith
  have hpos2 : 0 < (N ^ 2 - 1) ^ 2 := by positivity
  have e1 : 0 ≤ 1 / (N ^ 2 - 1) ^ 2 := (one_div_pos.2 hpos2).le
  replace h : N ^ 2 ≤ |Y - t| := h
  replace hf : f = true := hf
  subst hf
  cases p <;> simp only [wFactor, if_true, Bool.false_eq_true, if_false]
  · have hsq : (N ^ 2 - 1) ^ 2 ≤ (t - Y - 1) ^ 2 := by
      rcases le_abs.1 h with h | h
      · have : (t - Y - 1) ^ 2 = (Y - t + 1) ^ 2 := by ring
        rw [this]
        exact pow_le_pow_left₀ hpos.le (by linarith) 2
      · exact pow_le_pow_left₀ hpos.le (by linarith) 2
    have b1 : 1 / (t - Y - 1) ^ 2 ≤ 1 / (N ^ 2 - 1) ^ 2 := one_div_le_one_div_of_le hpos2 hsq
    have b2 : 0 ≤ 1 / (t - Y - 1) ^ 2 := by positivity
    constructor <;> linarith
  · constructor <;> linarith
end Formalism.FourierDecayAlt.P.ProductFactorBounds
