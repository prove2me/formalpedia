-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ProductFactorBounds.factor_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:40:11.241812+00:00
-- url     : https://prove2.me/submissions/f8122f72-e3c3-4c15-be31-00f527d36693

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
theorem _root_.solution (N : ℝ) (hN : 2 ≤ N) (l : WLetter ℝ) (Y : ℝ) (h : N ^ 2 ≤ |Y - l.pt|) :
    1 - 1 / N ^ 2 ≤ wFactor l Y ∧ wFactor l Y ≤ 1 + 1 / (N ^ 2 - 1) := by
  obtain ⟨p, t, f⟩ := l
  have hN2 : 4 ≤ N ^ 2 := by nlinarith
  have hN2p : 0 < N ^ 2 := by linarith
  have hpos : 0 < N ^ 2 - 1 := by linarith
  have e1 : 0 ≤ 1 / N ^ 2 := (one_div_pos.2 hN2p).le
  have e2 : 0 ≤ 1 / (N ^ 2 - 1) := (one_div_pos.2 hpos).le
  have e3 : 1 / N ^ 2 ≤ 1 / (N ^ 2 - 1) := one_div_le_one_div_of_le hpos (by linarith)
  replace h : N ^ 2 ≤ |Y - t| := h
  cases p <;> cases f <;> simp only [wFactor, if_true, Bool.false_eq_true, if_false]
  · rcases le_abs.1 h with h | h
    · have hx : 0 < Y - t + 1 := by linarith
      have hne : t - Y - 1 ≠ 0 := by
        intro e; linarith
      have e : (t - Y) / (t - Y - 1) = 1 - 1 / (Y - t + 1) := by
        field_simp
        ring
      have b1 : 1 / (Y - t + 1) ≤ 1 / N ^ 2 := one_div_le_one_div_of_le hN2p (by linarith)
      have b2 : 0 ≤ 1 / (Y - t + 1) := (one_div_pos.2 hx).le
      rw [e]
      constructor <;> linarith
    · have hx : 0 < t - Y - 1 := by linarith
      have e : (t - Y) / (t - Y - 1) = 1 + 1 / (t - Y - 1) := by
        field_simp
        ring
      have b1 : 1 / (t - Y - 1) ≤ 1 / (N ^ 2 - 1) := one_div_le_one_div_of_le hpos (by linarith)
      have b2 : 0 ≤ 1 / (t - Y - 1) := (one_div_pos.2 hx).le
      rw [e]
      constructor <;> linarith
  · have hsq : N ^ 2 ≤ (t - Y - 1) ^ 2 := by
      rcases le_abs.1 h with h | h
      · nlinarith
      · nlinarith
    have b1 : 1 / (t - Y - 1) ^ 2 ≤ 1 / N ^ 2 := one_div_le_one_div_of_le hN2p hsq
    have b2 : 0 ≤ 1 / (t - Y - 1) ^ 2 := by positivity
    constructor <;> linarith
  · rcases le_abs.1 h with h | h
    · have hx : 0 < Y - t := by linarith
      have e : (Y - t + 1) / (Y - t) = 1 + 1 / (Y - t) := by
        field_simp
      have b1 : 1 / (Y - t) ≤ 1 / N ^ 2 := one_div_le_one_div_of_le hN2p h
      have b2 : 0 ≤ 1 / (Y - t) := (one_div_pos.2 hx).le
      rw [e]
      constructor <;> linarith
    · have hx : 0 < t - Y := by linarith
      have hne : Y - t ≠ 0 := by
        intro e; linarith
      have e : (Y - t + 1) / (Y - t) = 1 - 1 / (t - Y) := by
        field_simp
        ring
      have b1 : 1 / (t - Y) ≤ 1 / N ^ 2 := one_div_le_one_div_of_le hN2p (by linarith)
      have b2 : 0 ≤ 1 / (t - Y) := (one_div_pos.2 hx).le
      rw [e]
      constructor <;> linarith
  · constructor <;> linarith
end Formalism.FourierDecayAlt.P.ProductFactorBounds
