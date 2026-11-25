-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.SumDat.rel_of_abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:17:44.440108+00:00
-- url     : https://prove2.me/submissions/e3937579-e774-4ca1-b2e8-14a381e9f515

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_FourTermSumBoundOfParameters
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_QuotientParamNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
namespace Formalism.MainNotions.Gaps.T0
namespace SumDat
theorem _root_.solution {ι : Type*} (X : SumDat ι) {CP Z PP : ℝ} (hCP : 1 ≤ CP) (hZ : 2 ≤ Z)
    (hPP : PP = CP * Z ^ 12) (hD : 1 ≤ X.D) (h1 : X.P1 ≤ CP * Z ^ 6) (h2 : X.P2 ≤ CP * Z ^ 5)
    (h3 : X.P3 ≤ CP * Z ^ 3) (h4 : X.P4 ≤ 2 * (CP * Z ^ 10) * (CP * Z ^ 4)) : X.Rel PP := by
  have hZ1 : 1 ≤ Z := by linarith
  have hZ0 : 0 ≤ Z := by linarith
  have hCP0 : 0 ≤ CP := by linarith
  have hPP2 : PP ^ 2 = CP ^ 2 * Z ^ 24 := by rw [hPP]; ring
  have hPP3 : PP ^ 3 = CP ^ 3 * Z ^ 36 := by rw [hPP]; ring
  have cp2 : CP ≤ CP ^ 2 := le_self_pow₀ hCP (by norm_num)
  have cp3 : CP ≤ CP ^ 3 := le_self_pow₀ hCP (by norm_num)
  have z6 : Z ^ 6 ≤ Z ^ 24 := pow_le_pow_right₀ hZ1 (by norm_num)
  have z5 : Z ^ 5 ≤ Z ^ 36 := pow_le_pow_right₀ hZ1 (by norm_num)
  have z3 : Z ^ 3 ≤ Z ^ 24 := pow_le_pow_right₀ hZ1 (by norm_num)
  have z14 : 2 * Z ^ 14 ≤ Z ^ 24 := by
    have a : (2 : ℝ) ≤ Z ^ 10 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hZ 10)
    calc 2 * Z ^ 14 ≤ Z ^ 10 * Z ^ 14 := mul_le_mul_of_nonneg_right a (by positivity)
      _ = Z ^ 24 := by ring
  have r1 : X.P1 * X.D ^ 2 ≤ PP ^ 2 * X.D ^ 3 := by
    have a : X.P1 ≤ PP ^ 2 :=
      h1.trans (by rw [hPP2]; exact mul_le_mul cp2 z6 (by positivity) (by positivity))
    have b : X.P1 * X.D ^ 2 ≤ PP ^ 2 * X.D ^ 2 := mul_le_mul_of_nonneg_right a (sq_nonneg _)
    have c : X.D ^ 2 ≤ X.D ^ 3 := pow_le_pow_right₀ hD (by norm_num)
    exact b.trans (mul_le_mul_of_nonneg_left c (sq_nonneg _))
  have r2 : X.P2 ≤ PP ^ 3 :=
    h2.trans (by rw [hPP3]; exact mul_le_mul cp3 z5 (by positivity) (by positivity))
  have r3 : X.P3 ≤ PP ^ 2 :=
    h3.trans (by rw [hPP2]; exact mul_le_mul cp2 z3 (by positivity) (by positivity))
  have r4 : X.P4 ≤ PP ^ 2 := by
    refine h4.trans ?_
    rw [hPP2, show 2 * (CP * Z ^ 10) * (CP * Z ^ 4) = CP ^ 2 * (2 * Z ^ 14) by ring]
    exact mul_le_mul_of_nonneg_left z14 (by positivity)
  exact ⟨r1, r2, r3, r4⟩
end SumDat
end Formalism.MainNotions.Gaps.T0
