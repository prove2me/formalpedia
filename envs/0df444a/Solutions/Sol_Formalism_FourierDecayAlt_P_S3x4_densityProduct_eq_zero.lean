-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x4.densityProduct_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:36.525826+00:00
-- url     : https://prove2.me/submissions/e560344b-7fd5-4af9-8ec4-bf5908dc5d1b

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
theorem _root_.solution (q : ℕ) (lo hi : ℤ) (h1 : lo ≤ 0) (h2 : 0 ≤ hi) : densP 1 q lo hi = 0 := by
  unfold densP
  exact Finset.prod_eq_zero (Finset.mem_Icc.mpr ⟨h1, h2⟩) (by simp)
end Formalism.FourierDecayAlt.P.S3x4
