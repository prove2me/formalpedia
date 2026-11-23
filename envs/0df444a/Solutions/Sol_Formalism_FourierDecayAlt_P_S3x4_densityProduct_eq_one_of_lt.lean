-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x4.densityProduct_eq_one_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:36.340706+00:00
-- url     : https://prove2.me/submissions/6b93c3e5-bb1d-4765-8e54-536cffe6eb56

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
theorem _root_.solution (q : ℕ) (lo hi : ℤ) (h : hi < lo) : densP 1 q lo hi = 1 := by
  unfold densP
  rw [Finset.Icc_eq_empty (by omega), Finset.prod_empty]
end Formalism.FourierDecayAlt.P.S3x4
