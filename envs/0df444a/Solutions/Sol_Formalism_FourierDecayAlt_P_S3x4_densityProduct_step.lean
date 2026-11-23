-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x4.densityProduct_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:37.207951+00:00
-- url     : https://prove2.me/submissions/bb182b06-ae99-4525-b171-d60180bcd934

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SplitFrameTransitive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x4
open Matrix Finset Module Formalism.FourierDecayAlt.S3
namespace Formalism.FourierDecayAlt.P.S3x4
theorem _root_.solution (q : ℕ) (lo hi : ℤ) (h : lo ≤ hi) :
    densP 1 q lo hi = (1 - (q : ℝ) ^ (-lo)) * densP 1 q (lo + 1) hi := by
  unfold densP
  rw [← Finset.insert_Icc_add_one_left_eq_Icc h, Finset.prod_insert (by simp)]
  simp
end Formalism.FourierDecayAlt.P.S3x4
