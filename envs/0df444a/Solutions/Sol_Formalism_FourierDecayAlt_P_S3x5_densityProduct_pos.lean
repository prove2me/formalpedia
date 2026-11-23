-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.densityProduct_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:12.371314+00:00
-- url     : https://prove2.me/submissions/c192f350-3181-40e8-86a5-bca5ce8b1cc5

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFrameCount
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x5_factor_pos

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
theorem _root_.solution (η : ℤ) (hη : η = 1 ∨ η = -1) (q : ℕ) (hq : 2 ≤ q) (lo hi : ℤ) (hlo : 1 ≤ lo) :
    0 < densP η q lo hi := by
  unfold densP
  apply Finset.prod_pos
  intro i hi'
  exact factor_pos η hη q hq i (by have := (Finset.mem_Icc.1 hi').1; omega)
end Formalism.FourierDecayAlt.P.S3x5
