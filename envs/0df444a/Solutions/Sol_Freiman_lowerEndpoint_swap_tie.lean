-- Prove2me | solution 1 for Freiman.lowerEndpoint_swap_tie
-- status  : ACCEPTED   (disprove)
-- author  : @cm_beta
-- created : 2026-09-19T07:05:34.89291+00:00
-- url     : https://prove2.me/submissions/c70c6339-830a-42d9-a4ac-bfcee0b97ac2

import Definitions.Def_Freiman_lowerCover
import Mathlib.Tactic

/-! A refutation of the unrestricted lowerEndpoint_swap_tie target.
The explicit witness is a = [2,4], b = [6,1], and upper = false. -/

open Freiman
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace Freiman.WidthTieCounterexample

private theorem sqrt21_bounds : (4 : ℝ) < Real.sqrt 21 ∧ Real.sqrt 21 < 5 := by
  have hn := Real.sqrt_nonneg (21 : ℝ)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)
  constructor <;> nlinarith

private theorem alpha_pos : 0 < lowerAlpha := by
  unfold lowerAlpha
  nlinarith [sqrt21_bounds.1]

private theorem beta_pos : 0 < lowerBeta := by
  unfold lowerBeta
  nlinarith [sqrt21_bounds.1]

private theorem alpha_lt_beta : lowerAlpha < lowerBeta := by
  unfold lowerAlpha lowerBeta
  nlinarith [sqrt21_bounds.1]

private theorem tau_pos : 0 < lowerTau := by
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  unfold lowerTau
  nlinarith

private theorem eval24 (x : ℝ) (hx : 0 ≤ x) :
    prefixEval [2,4] x = (x + 4) / (2*x + 9) := by
  norm_num [prefixEval]
  field_simp <;> nlinarith

private theorem eval61 (x : ℝ) (hx : 0 ≤ x) :
    prefixEval [6,1] x = (x + 1) / (6*x + 7) := by
  norm_num [prefixEval]
  field_simp <;> nlinarith

private theorem eval243 (x : ℝ) (hx : 0 ≤ x) :
    prefixEval [2,4,3] x = (4*x + 13) / (9*x + 29) := by
  norm_num [prefixEval]
  field_simp <;> nlinarith

private theorem eval613 (x : ℝ) (hx : 0 ≤ x) :
    prefixEval [6,1,3] x = (x + 4) / (7*x + 27) := by
  norm_num [prefixEval]
  field_simp <;> nlinarith

private theorem eval61213 (x : ℝ) (hx : 0 ≤ x) :
    prefixEval [6,1,2,1,3] x = (4*x + 15) / (27*x + 101) := by
  norm_num [prefixEval]
  field_simp <;> nlinarith

private theorem eval24213 (x : ℝ) (hx : 0 ≤ x) :
    prefixEval [2,4,2,1,3] x = (13*x + 48) / (29*x + 107) := by
  norm_num [prefixEval]
  field_simp <;> nlinarith

private theorem mobius_width (a b c d : ℝ)
    (hdet : |a*d - b*c| = 1)
    (hα : 0 < c*lowerAlpha+d) (hβ : 0 < c*lowerBeta+d) :
    |(a*lowerBeta+b)/(c*lowerBeta+d) - (a*lowerAlpha+b)/(c*lowerAlpha+d)| =
      (lowerBeta-lowerAlpha)/((c*lowerBeta+d)*(c*lowerAlpha+d)) := by
  have heq : (a*lowerBeta+b)/(c*lowerBeta+d) - (a*lowerAlpha+b)/(c*lowerAlpha+d) =
      (a*d-b*c)*(lowerBeta-lowerAlpha)/((c*lowerBeta+d)*(c*lowerAlpha+d)) := by
    have ha : lowerAlpha*c+d ≠ 0 := by nlinarith
    have hb : lowerBeta*c+d ≠ 0 := by nlinarith
    field_simp [ne_of_gt hα, ne_of_gt hβ, ha, hb]
    <;> ring
  rw [heq, abs_div, abs_mul, hdet, abs_of_pos (sub_pos.mpr alpha_lt_beta),
    abs_of_pos (mul_pos hβ hα), one_mul]

private theorem width24 :
    lowerWidth [2,4] = (lowerBeta-lowerAlpha)/(55+10*Real.sqrt 21) := by
  unfold lowerWidth
  rw [eval24 _ beta_pos.le, eval24 _ alpha_pos.le]
  have hm := mobius_width 1 4 2 9 (by norm_num)
    (by nlinarith [alpha_pos]) (by nlinarith [beta_pos])
  norm_num only [one_mul] at hm
  rw [hm]
  congr 1
  unfold lowerAlpha lowerBeta
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]

private theorem width61 :
    lowerWidth [6,1] = (lowerBeta-lowerAlpha)/(55+10*Real.sqrt 21) := by
  unfold lowerWidth
  rw [eval61 _ beta_pos.le, eval61 _ alpha_pos.le]
  have hm := mobius_width 1 1 6 7 (by norm_num)
    (by nlinarith [alpha_pos]) (by nlinarith [beta_pos])
  norm_num only [one_mul] at hm
  rw [hm]
  congr 1
  unfold lowerAlpha lowerBeta
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]

theorem width_tie : lowerWidth [2,4] = lowerWidth [6,1] := by rw [width24, width61]

private theorem width243 :
    lowerWidth [2,4,3] = (lowerBeta-lowerAlpha)/((1043+267*Real.sqrt 21)/2) := by
  unfold lowerWidth
  rw [eval243 _ beta_pos.le, eval243 _ alpha_pos.le]
  rw [mobius_width 4 13 9 29 (by norm_num)
    (by nlinarith [alpha_pos]) (by nlinarith [beta_pos])]
  congr 1
  unfold lowerAlpha lowerBeta
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]

private theorem width613 :
    lowerWidth [6,1,3] = (lowerBeta-lowerAlpha)/((947+203*Real.sqrt 21)/2) := by
  unfold lowerWidth
  rw [eval613 _ beta_pos.le, eval613 _ alpha_pos.le]
  have hm := mobius_width 1 4 7 27 (by norm_num)
    (by nlinarith [alpha_pos]) (by nlinarith [beta_pos])
  norm_num only [one_mul] at hm
  rw [hm]
  congr 1
  unfold lowerAlpha lowerBeta
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 21 by norm_num)]

private theorem shorten_direct : lowerWidth [2,4,3] ≤ (7/5 : ℝ)*lowerWidth [6,1,3] := by
  rw [width243, width613]
  have ht := sub_pos.mpr alpha_lt_beta
  have hs := Real.sqrt_nonneg (21 : ℝ)
  have hd1 : 0 < (1043+267*Real.sqrt (21 : ℝ))/2 := by positivity
  have hd2 : 0 < (947+203*Real.sqrt (21 : ℝ))/2 := by positivity
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hd1 hd2).mpr
  nlinarith [mul_nonneg ht.le hs]

private theorem shorten_swapped : lowerWidth [6,1,3] ≤ (7/5 : ℝ)*lowerWidth [2,4,3] := by
  rw [width243, width613]
  have ht := sub_pos.mpr alpha_lt_beta
  have hs := Real.sqrt_nonneg (21 : ℝ)
  have hd1 : 0 < (1043+267*Real.sqrt (21 : ℝ))/2 := by positivity
  have hd2 : 0 < (947+203*Real.sqrt (21 : ℝ))/2 := by positivity
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hd2 hd1).mpr
  nlinarith [mul_nonneg ht.le hs]

private theorem direct_words : lowerEndpointWords ([2,4],[6,1]) false =
    ([2,4,3],[6,1,2,1,3]) := by
  have hab : lowerWidth [6,1] ≤ lowerWidth [2,4] := width_tie.ge
  simp [lowerEndpointWords, lowerEqualWords, lowerNormalize, lowerNaturalShort,
    lowerEndpointSuffix, lowerEnds, hab, shorten_direct]
  decide +kernel

private theorem swapped_words : lowerEndpointWords ([6,1],[2,4]) false =
    ([6,1,3],[2,4,2,1,3]) := by
  have hab : lowerWidth [2,4] ≤ lowerWidth [6,1] := width_tie.le
  simp [lowerEndpointWords, lowerEqualWords, lowerNormalize, lowerNaturalShort,
    lowerEndpointSuffix, lowerEnds, hab, shorten_swapped]
  decide +kernel

private theorem eval243_tau : prefixEval [2,4,3] lowerTau =
    (72-Real.sqrt 3)/157 := by
  rw [eval243 _ tau_pos.le]
  unfold lowerTau
  have hs := Real.sqrt_nonneg (3 : ℝ)
  have hd : 9*(Real.sqrt (3 : ℝ)-1)+29 ≠ 0 := by nlinarith
  apply (div_eq_div_iff hd (by norm_num)).mpr
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

private theorem eval613_tau : prefixEval [6,1,3] lowerTau =
    (39-Real.sqrt 3)/253 := by
  rw [eval613 _ tau_pos.le]
  unfold lowerTau
  have hs := Real.sqrt_nonneg (3 : ℝ)
  have hd : 7*(Real.sqrt (3 : ℝ)-1)+27 ≠ 0 := by nlinarith
  apply (div_eq_div_iff hd (by norm_num)).mpr
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

private theorem eval61213_tau : prefixEval [6,1,2,1,3] lowerTau =
    (490-Real.sqrt 3)/3289 := by
  rw [eval61213 _ tau_pos.le]
  unfold lowerTau
  have hs := Real.sqrt_nonneg (3 : ℝ)
  have hd : 27*(Real.sqrt (3 : ℝ)-1)+101 ≠ 0 := by nlinarith
  apply (div_eq_div_iff hd (by norm_num)).mpr
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

private theorem eval24213_tau : prefixEval [2,4,2,1,3] lowerTau =
    (1599-Real.sqrt 3)/3561 := by
  rw [eval24213 _ tau_pos.le]
  unfold lowerTau
  have hs := Real.sqrt_nonneg (3 : ℝ)
  have hd : 29*(Real.sqrt (3 : ℝ)-1)+107 ≠ 0 := by nlinarith
  apply (div_eq_div_iff hd (by norm_num)).mpr
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

theorem direct_endpoint : lowerEndpoint ([2,4],[6,1]) false =
    (2379230-3446*Real.sqrt 3)/516373 := by
  unfold lowerEndpoint
  rw [direct_words]
  dsimp only
  rw [eval243_tau, eval61213_tau]
  ring

theorem swapped_endpoint : lowerEndpoint ([6,1],[2,4]) false =
    (4147158-3814*Real.sqrt 3)/900933 := by
  unfold lowerEndpoint
  rw [swapped_words]
  dsimp only
  rw [eval613_tau, eval24213_tau]
  ring

theorem endpoint_strict : lowerEndpoint ([6,1],[2,4]) false <
    lowerEndpoint ([2,4],[6,1]) false := by
  rw [direct_endpoint, swapped_endpoint]
  have hn := Real.sqrt_nonneg (3 : ℝ)
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hb : Real.sqrt (3 : ℝ) < 7/4 := by nlinarith
  linarith

end Freiman.WidthTieCounterexample

theorem solution : ¬ (∀ (a b : List ℕ+) (u : Bool), lowerWidth a = lowerWidth b →
    lowerEndpoint (a,b) u = lowerEndpoint (b,a) u) := by
  intro h
  have he := h [2,4] [6,1] false Freiman.WidthTieCounterexample.width_tie
  exact (ne_of_gt Freiman.WidthTieCounterexample.endpoint_strict) he
