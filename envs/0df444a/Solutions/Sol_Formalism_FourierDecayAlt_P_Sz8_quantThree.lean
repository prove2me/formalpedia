-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz8.quantThree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:40.67985+00:00
-- url     : https://prove2.me/submissions/35fa29db-bca6-434c-8874-c6a9ac815324

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CmRingIdempotentUnitRatioIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.Sz Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.Sz8
namespace Formalism.FourierDecayAlt.P.Sz8
theorem _root_.solution (x E P M sT : ℝ) (hx : 1 ≤ x) (hPE : P ^ 2 ≤ E) (hM : 0 < M)
    (hMx : M ^ 2 ≤ x) (hsT : x * E ≤ sT) :
    P ≤ Real.sqrt (sT / (M * Real.sqrt x)) := by
  have hx0 : 0 < x := by linarith
  rcases le_or_gt P 0 with hP | hP
  · have : 0 ≤ Real.sqrt (sT / (M * Real.sqrt x)) := Real.sqrt_nonneg _
    linarith
  apply Real.le_sqrt_of_sq_le
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  rw [le_div_iff₀ (by positivity)]
  have hMs : M ≤ Real.sqrt x := Real.le_sqrt_of_sq_le hMx
  have hMsx : M * Real.sqrt x ≤ x := by
    calc M * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x := mul_le_mul_of_nonneg_right hMs hsx.le
      _ = x := Real.mul_self_sqrt hx0.le
  have hE : 0 ≤ E := le_trans (sq_nonneg P) hPE
  have := mul_le_mul hPE hMsx (by positivity) hE
  nlinarith
end Formalism.FourierDecayAlt.P.Sz8
