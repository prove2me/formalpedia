-- Prove2me | solution 1 for Formalism.DimensionVariation.division_inequality_two_constants
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:29.766999+00:00
-- url     : https://prove2.me/submissions/b3c67bbd-5072-4189-818b-cacf71d44fbe

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_TheoremDivIneq
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqExplicit6
import Definitions.Def_Formalism_ThetaSupremumBounds_FinalJ
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_GlobalBoundRefinements
import Theorems.Thm_Formalism_DimensionVariation_division_inequality_explicit

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
theorem _root_.solution : DivIneqTwoConst6 := by
  intro J Pl _ _ TT _ r ν muC mu0 Fo hu hP mlam logT aT fa x eps L b a rd La B0 Nc m f k N S tt η
    w'' b' lam0 C0 c Lpass Eb e6 eP logOm pq w eE δ
  intro q1 q2 q3 q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z13 z14 z15 z16 z17 z18 z19 z20 z21
    z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC1 hCc y1 y2 y3 y4 y5 y6
  have hC0 : 0 < C0 := by linarith
  have hxe : 0 ≤ x ^ eps := Real.rpow_nonneg (by linarith) _
  have hr : 1 ≤ c / C0 := (one_le_div hC0).mpr hCc
  have hb : 0 ≤ b := by rw [z4]; exact (Real.exp_pos _).le
  have hB0 : 0 ≤ B0 := by rw [z10]; positivity
  have key := division_inequality_explicit J Pl TT r ν muC mu0 Fo hu hP mlam logT aT fa x eps L b a rd La B0 Nc
    (c / C0 * x ^ eps) m f k N S tt η w'' b' lam0 C0 Lpass Eb e6 eP logOm pq w eE δ
    q1 q2 q3 q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 (le_mul_of_one_le_left hxe hr)
    z13 z14 z15 z16 z17 z18 z19 z20 z21
    z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC0.le y1
    (by
      have : C0 * m * (c / C0 * x ^ eps) * (B0 + Nc) = c * m * x ^ eps * (B0 + Nc) := by
        field_simp
      rw [this]; exact y2) y3 y4 y5 y6
  have hY : 0 ≤ m * (B0 + Nc) * x ^ eps := by positivity
  have h1 : (50 * C0 + 10) * (m * (B0 + Nc) * (c / C0 * x ^ eps)) =
      (50 * c + 10 * (c / C0)) * (m * (B0 + Nc) * x ^ eps) := by
    field_simp
  have h2 : c / C0 ≤ c := div_le_self (by linarith) hC1
  have h3 : (50 * c + 10 * (c / C0)) * (m * (B0 + Nc) * x ^ eps) ≤
      60 * c * (m * (B0 + Nc) * x ^ eps) := mul_le_mul_of_nonneg_right (by linarith) hY
  have h4 : (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + Nc) * (c / C0 * x ^ eps)) =
      (50 * C0 + 10) * ((TT.card : ℝ) * a * La) +
        (50 * C0 + 10) * (m * (B0 + Nc) * (c / C0 * x ^ eps)) := by ring
  rw [h4, h1] at key
  linarith
end Formalism.DimensionVariation
