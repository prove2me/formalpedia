-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz8.sqrtTTLower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:41.599092+00:00
-- url     : https://prove2.me/submissions/796dc278-960b-4daf-95f7-ed2ff366dde7

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
theorem _root_.solution (x bb cT Cb mr TT : ℝ) (hx : 1 ≤ x) (hcT : 0 < cT) (hCb : 0 < Cb) (hm : 2 ≤ mr)
    (hbb : x ^ (Cb / 2) ≤ bb) (hTT : (bb ^ (cT * mr)) ^ 2 ≤ TT) :
    x * x ^ (cT * Cb - 1) ≤ Real.sqrt TT := by
  have hx0 : 0 < x := by linarith
  have hbb0 : 0 < bb := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hbb
  have e1 : x * x ^ (cT * Cb - 1) = x ^ (cT * Cb) := by
    conv_lhs => arg 1; rw [← Real.rpow_one x]
    rw [← Real.rpow_add hx0]; ring_nf
  rw [e1]
  have hs : bb ^ (cT * mr) ≤ Real.sqrt TT := by
    apply Real.le_sqrt_of_sq_le; exact hTT
  have h2 : (x ^ (Cb / 2)) ^ (cT * mr) ≤ bb ^ (cT * mr) :=
    Real.rpow_le_rpow (by positivity) hbb (by positivity)
  have h3 : (x ^ (Cb / 2)) ^ (cT * mr) = x ^ (Cb / 2 * (cT * mr)) := by
    rw [← Real.rpow_mul hx0.le]
  have h4 : x ^ (cT * Cb) ≤ x ^ (Cb / 2 * (cT * mr)) := by
    apply Real.rpow_le_rpow_of_exponent_le hx
    have : cT * Cb * 2 ≤ cT * Cb * mr := mul_le_mul_of_nonneg_left hm (by positivity)
    nlinarith
  linarith
end Formalism.FourierDecayAlt.P.Sz8
