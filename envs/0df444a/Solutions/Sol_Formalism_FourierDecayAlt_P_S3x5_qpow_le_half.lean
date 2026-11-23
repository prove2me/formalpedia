-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.qpow_le_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:25:22.405824+00:00
-- url     : https://prove2.me/submissions/851bb023-1803-485b-ac9f-804ce0c5afbf

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x5
open Finset Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x5
theorem _root_.solution (q : ℕ) (hq : 2 ≤ q) (i : ℤ) (hi : 1 ≤ i) : (q : ℝ) ^ (-i) ≤ 1 / 2 := by
  have hq' : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have h1 : (q : ℝ) ^ (-i) ≤ (q : ℝ) ^ (-1 : ℤ) :=
    zpow_le_zpow_right₀ (by linarith) (by omega)
  have h2 : (q : ℝ) ^ (-1 : ℤ) ≤ 1 / 2 := by
    rw [zpow_neg_one, one_div]
    exact inv_anti₀ (by norm_num) hq'
  linarith
end Formalism.FourierDecayAlt.P.S3x5
