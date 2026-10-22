-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.tHess_det_pos_mu_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T17:35:24.411904+00:00
-- url     : https://prove2.me/submissions/bc99ecd7-15da-48fe-ae9a-d97d7d5f29a9

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Theorems.Thm_det_quaternionFrame_eq_bordered
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_radial_poly_pos
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_radial_derivative_pos_of_reduced
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_mu_zero_univariate
import Theorems.Thm_adjugate_symm_fin_four
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_tHessR_mu_zero_frame
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_bordered_mu_zero_eq
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_bordered_mu_zero_fiber
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_fiber_circle_bound
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian in
theorem solution (c r : ℝ) (s : Phase)
    (hc0 : 21 / 10 ≤ c) (hc1 : c ≤ 21 / 10 + 1 / 1000000)
    (hr : 0 < r) (hr2 : r ^ 2 = secondCollisionDistanceSq s)
    (hK : pP 0 c s - 0 * (zNormSq s / r) = 0)
    (hz : 2 * zNormSq s ≤ 3 / 5) :
    0 < (tHessR 0 c r s).det := by
  have hK1 : pP 0 c s = 0 := by simpa using hK
  have hK2 := hK1
  unfold pP wNormSq zNormSq at hK2
  -- (C) chain: s · ∇K > 0, hence ∇K ≠ 0
  have hZ0 : 0 ≤ zNormSq s := by unfold zNormSq; positivity
  have hu1 : uCoord s ≤ zNormSq s := by unfold uCoord zNormSq; nlinarith [sq_nonneg (s 1)]
  have hu2 : -zNormSq s ≤ uCoord s := by unfold uCoord zNormSq; nlinarith [sq_nonneg (s 0)]
  have hr2' : r ^ 2 = 4 * zNormSq s ^ 2 - 4 * uCoord s + 1 := by
    rw [hr2]; unfold secondCollisionDistanceSq zNormSq uCoord; ring
  have hρ : (1 - 2 * c * (s 0 ^ 2 + s 1 ^ 2) + 4 * (s 0 ^ 2 + s 1 ^ 2) ^ 3) = ((s 2 - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 1) ^ 2 + (s 3 + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 0) ^ 2) := by linear_combination (-2) * hK2
  have hρ0 : 0 ≤ ((s 2 - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 1) ^ 2 + (s 3 + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 0) ^ 2) := by positivity
  have hR : 0 ≤ radrR2 0 c (zNormSq s) (uCoord s) r := by
    have e : radrR2 0 c (zNormSq s) (uCoord s) r = r * (1 - 2 * c * (s 0 ^ 2 + s 1 ^ 2) + 4 * (s 0 ^ 2 + s 1 ^ 2) ^ 3) := by unfold radrR2 zNormSq; ring
    rw [e, hρ]; positivity
  have hpoly := radial_poly_pos 0 c (zNormSq s) (uCoord s) r le_rfl (by norm_num) hc0 hc1 hZ0
    (by linarith) hu1 hu2 hr hr2' hR
  have hsg := radial_derivative_pos_of_reduced 0 c r s hr hK hpoly
  have hg2 : 0 < ![kGradR 0 c r s 0, kGradR 0 c r s 1, kGradR 0 c r s 2, kGradR 0 c r s 3] ⬝ᵥ ![kGradR 0 c r s 0, kGradR 0 c r s 1, kGradR 0 c r s 2, kGradR 0 c r s 3] := by
    simp [dotProduct, Fin.sum_univ_four]
    rw [Fin.sum_univ_four] at hsg
    by_contra hneg
    push_neg at hneg
    have e0 : kGradR 0 c r s 0 = 0 := by nlinarith [sq_nonneg (kGradR 0 c r s 0), sq_nonneg (kGradR 0 c r s 1), sq_nonneg (kGradR 0 c r s 2), sq_nonneg (kGradR 0 c r s 3)]
    have e1 : kGradR 0 c r s 1 = 0 := by nlinarith [sq_nonneg (kGradR 0 c r s 0), sq_nonneg (kGradR 0 c r s 1), sq_nonneg (kGradR 0 c r s 2), sq_nonneg (kGradR 0 c r s 3)]
    have e2 : kGradR 0 c r s 2 = 0 := by nlinarith [sq_nonneg (kGradR 0 c r s 0), sq_nonneg (kGradR 0 c r s 1), sq_nonneg (kGradR 0 c r s 2), sq_nonneg (kGradR 0 c r s 3)]
    have e3 : kGradR 0 c r s 3 = 0 := by nlinarith [sq_nonneg (kGradR 0 c r s 0), sq_nonneg (kGradR 0 c r s 1), sq_nonneg (kGradR 0 c r s 2), sq_nonneg (kGradR 0 c r s 3)]
    rw [e0, e1, e2, e3] at hsg
    simp at hsg
  rw [tHessR_mu_zero_frame, det_quaternionFrame_eq_bordered, adjugate_symm_fin_four]
  apply mul_pos (pow_pos hg2 2)
  rw [bordered_mu_zero_eq, bordered_mu_zero_fiber c s hK1]
  have hU := mu_zero_univariate (s 0 ^ 2 + s 1 ^ 2) c (by positivity) (by unfold zNormSq at hz; linarith) hc0 hc1
  exact fiber_circle_bound (s 2 - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 1) (s 3 + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 0) ((s 2 - 2 * (s 0 ^ 2 + s 1 ^ 2) * s 1) ^ 2 + (s 3 + 2 * (s 0 ^ 2 + s 1 ^ 2) * s 0) ^ 2) (s 0 ^ 2 + s 1 ^ 2) (s 0 ^ 2 - s 1 ^ 2) (s 0 * s 1) (s 0 ^ 2) (352*c^2*(s 0)^6 + 800*c^2*(s 0)^4*(s 1)^2 + 544*c^2*(s 0)^2*(s 1)^4 + 96*c^2*(s 1)^6 + 4*c^2 - 1920*c*(s 0)^10 - 8576*c*(s 0)^8*(s 1)^2 - 15104*c*(s 0)^6*(s 1)^4 - 13056*c*(s 0)^4*(s 1)^6 - 336*c*(s 0)^4 - 5504*c*(s 0)^2*(s 1)^8 - 416*c*(s 0)^2*(s 1)^2 - 896*c*(s 1)^10 - 80*c*(s 1)^4 + 1920*(s 0)^14 + 12416*(s 0)^12*(s 1)^2 + 34176*(s 0)^10*(s 1)^4 + 51840*(s 0)^8*(s 1)^6 + 1104*(s 0)^8 + 46720*(s 0)^6*(s 1)^8 + 3904*(s 0)^6*(s 1)^2 + 24960*(s 0)^4*(s 1)^10 + 5088*(s 0)^4*(s 1)^4 + 7296*(s 0)^2*(s 1)^12 + 2880*(s 0)^2*(s 1)^6 + 48*(s 0)^2 + 896*(s 1)^14 + 592*(s 1)^8 - 16*(s 1)^2) (48*c^2*(s 0)^2*(s 1) + 48*c^2*(s 1)^3 - 704*c*(s 0)^6*(s 1) - 2112*c*(s 0)^4*(s 1)^3 - 2112*c*(s 0)^2*(s 1)^5 - 704*c*(s 1)^7 - 32*c*(s 1) + 960*(s 0)^10*(s 1) + 4800*(s 0)^8*(s 1)^3 + 9600*(s 0)^6*(s 1)^5 + 9600*(s 0)^4*(s 1)^7 + 384*(s 0)^4*(s 1) + 4800*(s 0)^2*(s 1)^9 + 768*(s 0)^2*(s 1)^3 + 960*(s 1)^11 + 384*(s 1)^5) (-48*c^2*(s 0)^3 - 48*c^2*(s 0)*(s 1)^2 + 704*c*(s 0)^7 + 2112*c*(s 0)^5*(s 1)^2 + 2112*c*(s 0)^3*(s 1)^4 + 704*c*(s 0)*(s 1)^6 + 32*c*(s 0) - 960*(s 0)^11 - 4800*(s 0)^9*(s 1)^2 - 9600*(s 0)^7*(s 1)^4 - 9600*(s 0)^5*(s 1)^6 - 384*(s 0)^5 - 4800*(s 0)^3*(s 1)^8 - 768*(s 0)^3*(s 1)^2 - 960*(s 0)*(s 1)^10 - 384*(s 0)*(s 1)^4) (224 * (s 0 ^ 2 + s 1 ^ 2) ^ 7 - 224 * c * (s 0 ^ 2 + s 1 ^ 2) ^ 5 + 148 * (s 0 ^ 2 + s 1 ^ 2) ^ 4 + 24 * c ^ 2 * (s 0 ^ 2 + s 1 ^ 2) ^ 3 - 20 * c * (s 0 ^ 2 + s 1 ^ 2) ^ 2 - 4 * (s 0 ^ 2 + s 1 ^ 2) + c ^ 2) (60 * (s 0 ^ 2 + s 1 ^ 2) ^ 5 - 44 * c * (s 0 ^ 2 + s 1 ^ 2) ^ 3 + 24 * (s 0 ^ 2 + s 1 ^ 2) ^ 2 + 3 * c ^ 2 * (s 0 ^ 2 + s 1 ^ 2) - 2 * c) (1 - 2 * c * (s 0 ^ 2 + s 1 ^ 2) + 4 * (s 0 ^ 2 + s 1 ^ 2) ^ 3) c
    hρ hρ0 rfl (by positivity) (by ring) (by ring) (by ring) (by ring) hU.1 hU.2
