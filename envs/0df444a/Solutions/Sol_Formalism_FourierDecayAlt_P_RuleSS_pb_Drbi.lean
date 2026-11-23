-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleSS.pb_Drbi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:52.069885+00:00
-- url     : https://prove2.me/submissions/316e4831-4d79-4276-b40a-93e52c19f91a

import Definitions.Def_Formalism_HermitianCurvature_StatementR
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RuleSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_RuleSS_ofFn_shift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RuleSS
open Matrix Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData
variable {A : Type} [Ring A] [Algebra ℂ A]
variable {r : ℕ} (L : LevelData A r)
namespace Formalism.FourierDecayAlt.P.RuleSS
theorem _root_.solution (l) : L.pb l * L.Drbi = L.Drbi * (L.pb l + algebraMap ℂ A (-1)) := by
  have h := ofFn_shift (L.pb l) r L.cbi (fun m => if l = m then -1 else 0) (fun m => by
    rw [L.pb_cbi]; split_ifs <;> simp [mul_add, sub_eq_add_neg])
  rw [show (∑ m : Fin r, if l = m then (-1:ℂ) else 0) = -1 by simp] at h
  exact h
end Formalism.FourierDecayAlt.P.RuleSS
