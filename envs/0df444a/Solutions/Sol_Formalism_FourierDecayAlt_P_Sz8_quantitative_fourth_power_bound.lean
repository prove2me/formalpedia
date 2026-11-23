-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Sz8.quantitative_fourth_power_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:41:41.415297+00:00
-- url     : https://prove2.me/submissions/db2bc239-b92a-486f-b581-c970944f5bc1

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
theorem _root_.solution (x fr mr K P V s Del : ℝ) (hx : 1 ≤ x) (hm : 0 < mr) (hmf : mr ≤ fr)
    (hf : 1 ≤ fr) (hP : 0 ≤ P) (hPK : P ≤ K) (hV : 0 < V) (hVx : 40 * V ≤ x) (hs0 : 0 ≤ s)
    (hs : s ≤ x) (hDel : x ^ 4 * fr ^ 4 * K ≤ Del) :
    P * (V * s * (10 * mr)) ≤ Del / 4 := by
  have hx0 : 0 < x := by linarith
  have hK : 0 ≤ K := le_trans hP hPK
  have hV' : V ≤ x / 40 := by linarith
  have h1 : V * s ≤ x / 40 * x := mul_le_mul hV' hs hs0 (by linarith)
  have h2 : V * s * (10 * mr) ≤ x / 40 * x * (10 * fr) :=
    mul_le_mul h1 (by linarith) (by linarith) (by positivity)
  have h3 : P * (V * s * (10 * mr)) ≤ K * (x / 40 * x * (10 * fr)) :=
    mul_le_mul hPK h2 (by positivity) hK
  have hx2 : x ^ 2 ≤ x ^ 4 := pow_le_pow_right₀ hx (by norm_num)
  have hf1 : fr ≤ fr ^ 4 := by
    calc fr = fr ^ 1 := (pow_one fr).symm
      _ ≤ fr ^ 4 := pow_le_pow_right₀ hf (by norm_num)
  have h4 : K * (x / 40 * x * (10 * fr)) ≤ x ^ 4 * fr ^ 4 * K / 4 := by
    have : x ^ 2 * fr ≤ x ^ 4 * fr ^ 4 := mul_le_mul hx2 hf1 (by linarith) (by positivity)
    have := mul_le_mul_of_nonneg_left this hK
    nlinarith
  linarith
end Formalism.FourierDecayAlt.P.Sz8
