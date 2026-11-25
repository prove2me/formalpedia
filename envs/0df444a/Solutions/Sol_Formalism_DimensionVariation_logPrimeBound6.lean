-- Prove2me | solution 1 for Formalism.DimensionVariation.logPrimeBound6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:23:09.841204+00:00
-- url     : https://prove2.me/submissions/ee844f4b-be24-41e7-ba17-5fda21331953

import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
namespace Formalism.DimensionVariation
theorem _root_.solution (x L b a rd La g nV L' Cg : ℝ) (hx : 1 ≤ x) (hb : b = Real.exp L)
    (ha : a = x * b) (hrd : 1 ≤ rd) (hLa : La = Real.log (a * rd)) (hg : 0 < g) (hgl : Real.log g ≤ Cg * L)
    (hn : 0 < nV) (hnl : Real.log nV ≤ L) (hCg : 0 ≤ Cg) (hL' : L' = Real.log (b * rd * g * nV)) :
    L' ≤ (2 + Cg) * La := by
  have hbpos : 0 < b := by rw [hb]; exact Real.exp_pos _
  have hx0 : 0 < x := by linarith
  have hr0 : 0 < rd := by linarith
  have e1 : La = Real.log x + L + Real.log rd := by
    rw [hLa, ha, Real.log_mul (by positivity) hr0.ne', Real.log_mul hx0.ne' hbpos.ne', hb, Real.log_exp]
  have e2 : L' = L + Real.log rd + Real.log g + Real.log nV := by
    rw [hL', Real.log_mul (by positivity) hn.ne', Real.log_mul (by positivity) hg.ne',
      Real.log_mul hbpos.ne' hr0.ne', hb, Real.log_exp]
  have h1 := Real.log_nonneg hx
  have h2 := Real.log_nonneg hrd
  rw [e1, e2]
  nlinarith [mul_nonneg hCg h1, mul_nonneg hCg h2]
end Formalism.DimensionVariation
