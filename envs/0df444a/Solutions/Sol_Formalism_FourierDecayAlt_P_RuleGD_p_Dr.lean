-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.p_Dr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:04.627974+00:00
-- url     : https://prove2.me/submissions/afc7f2fa-41ee-48b9-9742-f6b45c8a178d

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleGD
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleGD_shift_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleGD
open Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Matrix
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
namespace Formalism.FourierDecayAlt.P.RuleGD
theorem _root_.solution (L : LevelData A r) (l : Fin r) : L.p l * L.Dr = L.Dr * L.p l + 1 * L.Dr := by
  have := shift_prod L.c (L.p l) (fun i => if l = i then (1 : ℂ) else 0) (fun i => by
    rw [L.p_c]; split_ifs <;> simp)
  simpa [LevelData.Dr] using this
end Formalism.FourierDecayAlt.P.RuleGD
