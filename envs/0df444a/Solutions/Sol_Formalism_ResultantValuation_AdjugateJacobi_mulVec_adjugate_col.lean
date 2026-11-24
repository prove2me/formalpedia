-- Prove2me | solution 1 for Formalism.ResultantValuation.AdjugateJacobi.mulVec_adjugate_col
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:36:41.210921+00:00
-- url     : https://prove2.me/submissions/040085bc-3cb1-43ce-926d-3d778e3725ea

import Definitions.Def_Formalism_ResultantValuation_KoszulSecondDifferential
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Adjugate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.ResultantValuation
open Formalism.ResultantValuation.AdjugateJacobi
variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
namespace Formalism.ResultantValuation.AdjugateJacobi
theorem _root_.solution (M : Matrix n n R) (l : n) :
    M *ᵥ (fun r => M.adjugate r l) = M.det • Pi.single l 1 := by
  ext a
  have := congrFun (congrFun (mul_adjugate M) a) l
  rw [mul_apply, Matrix.smul_apply, one_apply, smul_eq_mul] at this
  simp only [mulVec, dotProduct, this, Pi.smul_apply, Pi.single_apply, smul_eq_mul, eq_comm]
end Formalism.ResultantValuation.AdjugateJacobi
