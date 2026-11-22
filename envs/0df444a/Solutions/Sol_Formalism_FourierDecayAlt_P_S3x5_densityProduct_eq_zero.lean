-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x5.densityProduct_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:57:10.349329+00:00
-- url     : https://prove2.me/submissions/03c3f0db-6660-44f8-811c-5b117c0a1694

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
theorem _root_.solution (η : ℤ) (q : ℕ) (lo hi : ℤ) (h1 : lo ≤ 0) (h2 : 0 ≤ hi) : densP η q lo hi = 0 := by
  unfold densP
  apply Finset.prod_eq_zero (i := (0 : ℤ)) (Finset.mem_Icc.2 ⟨h1, h2⟩)
  simp
end Formalism.FourierDecayAlt.P.S3x5
