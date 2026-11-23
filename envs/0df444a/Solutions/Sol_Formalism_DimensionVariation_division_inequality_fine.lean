-- Prove2me | solution 1 for Formalism.DimensionVariation.division_inequality_fine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:29.444805+00:00
-- url     : https://prove2.me/submissions/8739bad3-d6bc-4789-94f1-ad3e7a2f9c0d

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
theorem _root_.solution : DivIneqFine6 := by
  intro J Pl _ _ TT _ r ν muC mu0 Fo hu hP mlam logT aT fa x eps L b a rd La B0 Nc m f k N S tt η
    w'' b' lam0 C0 c Lpass Eb e6 eP logOm pq w eE δ q1 q2 q3 q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10
    z11 z13 z14 z15 z16 z17 z18 z19 z20 z21 z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC y1 y2
    y3 y4 y5 y6
  have hxe : 0 ≤ x ^ eps := Real.rpow_nonneg (by linarith) _
  have hb : 0 ≤ b := by rw [z4]; exact (Real.exp_pos _).le
  have hB0 : 0 ≤ B0 := by rw [z10]; positivity
  have key := division_inequality_explicit J Pl TT r ν (muC - Eb) (mu0 - Eb) Fo hu hP mlam logT aT fa x eps L b a
    rd La B0 0 (x ^ eps) m f k N S tt η w'' b' lam0 C0 Lpass 0 e6 eP logOm pq w eE δ
    (by linarith) (by linarith) q3 q4 q5 q6 q7 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 le_rfl le_rfl
    z13 z14 z15 z16 z17 z18 z19 z20 z21
    z23 z24 z25 z26 z27 z28 z29 z30 z31 z32 z33 z34 z35 hC y1 (by positivity) y3 y4 y5 y6
  have h1 : 0 ≤ m * (Real.log x ^ 2 * Nc) := by positivity
  have h2 : (50 * C0 + 10) * (m * (B0 + 0) * x ^ eps) ≤
      (50 * C0 + 10) * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc)) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    nlinarith
  have h3 : (50 * C0 + 10) * ((TT.card : ℝ) * a * La + m * (B0 + 0) * x ^ eps) =
      (50 * C0 + 10) * ((TT.card : ℝ) * a * La) + (50 * C0 + 10) * (m * (B0 + 0) * x ^ eps) := by ring
  have h4 : (50 * C0 + 10 + c) * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc)) =
      (50 * C0 + 10) * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc)) +
        c * (m * (x ^ eps * B0 + Real.log x ^ 2 * Nc)) := by ring
  rw [h3] at key
  rw [h4]
  linarith
end Formalism.DimensionVariation
