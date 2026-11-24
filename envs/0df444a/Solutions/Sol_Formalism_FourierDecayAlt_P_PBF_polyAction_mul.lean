-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBF.polyAction_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:20:05.044389+00:00
-- url     : https://prove2.me/submissions/06b5a5c1-0e14-4209-99f9-c24d8768f112

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PrStarFst
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBF_pr_mul_fst
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBF_pr_sum_fst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBF
open Finset Formalism.FourierDecayAlt.Wd
variable {V : Type} [AddCommGroup V] [Module ℂ V] {S : Type} [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.PBF
theorem _root_.solution (M N : SlopeTestRemainingChoices S (Q.Pr V)) (X : Ix S → V) : actP (M * N) X = actP M (actP N X) := by
  funext a
  unfold actP
  simp only [Matrix.mul_apply, pr_sum_fst, pr_mul_fst, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  exact Finset.sum_comm
end Formalism.FourierDecayAlt.P.PBF
