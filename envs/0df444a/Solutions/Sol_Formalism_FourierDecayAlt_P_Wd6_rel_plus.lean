-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.rel_plus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:49:37.171167+00:00
-- url     : https://prove2.me/submissions/51aeca0f-01c0-467e-b572-1561a22b84f0

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_relT
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_weyl_ci

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd6
theorem _root_.solution {σ : Site A} (hσ : IsSite σ) (Y Ya : K) : Rel (Ts σ Y) (Ts σ Ya) (Y - Ya) := by
  have hw := hσ.1
  refine relT _ _ _ _ _ _ ?_ ?_ ?_
  · rw [hw.2.2]; module
  · rw [weyl_ci hw]; module
  · rw [hw.1, hw.2.1]
end Formalism.FourierDecayAlt.P.Wd6
