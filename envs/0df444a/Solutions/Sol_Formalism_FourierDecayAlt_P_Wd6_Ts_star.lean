-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.Ts_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:39.057559+00:00
-- url     : https://prove2.me/submissions/eca71704-5265-4451-b234-6d188cab900e

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix

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
theorem _root_.solution (σ : Site A) {Y : K} (hY : star Y = Y) :
    (Ts σ Y).map star = Tm Y (star σ.p) (star σ.c) (star σ.ci) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Ts, Tm, ← algebraMap_star_comm, hY]
end Formalism.FourierDecayAlt.P.Wd6
