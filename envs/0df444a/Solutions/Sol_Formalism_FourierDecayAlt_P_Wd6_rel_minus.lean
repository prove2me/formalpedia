-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd6.rel_minus
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:13.030896+00:00
-- url     : https://prove2.me/submissions/e1a6f221-3ea2-47fb-bc72-fa52a0262f85

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_relT
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_Ts_star
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
theorem _root_.solution {σ : Site A} (hσ : IsSite σ) {Y Yb : K} (hY : star Y = Y) (hYb : star Yb = Yb) :
    Rel ((Ts σ Y).map star) ((Ts σ Yb).map star) (Yb - Y) := by
  have hw := hσ.1
  rw [Ts_star σ hY, Ts_star σ hYb]
  refine relT _ _ _ _ _ _ ?_ ?_ ?_
  · have : star σ.c * star σ.p = star σ.p * star σ.c + star σ.c := by
      rw [← star_mul, ← star_mul, ← star_add, hw.2.2]
    rw [this]; module
  · have : star σ.ci * star σ.p = star σ.p * star σ.ci - star σ.ci := by
      rw [← star_mul, ← star_mul, ← star_sub, weyl_ci hw]
    rw [this]; module
  · rw [← star_mul, ← star_mul, hw.1, hw.2.1]
end Formalism.FourierDecayAlt.P.Wd6
