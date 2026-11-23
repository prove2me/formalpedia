-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleGD.pb_Drb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:06:04.619975+00:00
-- url     : https://prove2.me/submissions/7013495e-7d4b-4b73-8d35-8de2a56a8e91

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
theorem _root_.solution (L : LevelData A r) (l : Fin r) : L.pb l * L.Drb = L.Drb * L.pb l + 1 * L.Drb := by
  have := shift_prod L.cb (L.pb l) (fun i => if l = i then (1 : ℂ) else 0) (fun i => by
    rw [L.pb_cb]; split_ifs <;> simp)
  simpa [LevelData.Drb] using this
end Formalism.FourierDecayAlt.P.RuleGD
