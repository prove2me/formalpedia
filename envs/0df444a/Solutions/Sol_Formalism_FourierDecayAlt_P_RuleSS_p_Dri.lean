-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RuleSS.p_Dri
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:52.114148+00:00
-- url     : https://prove2.me/submissions/4897edc1-336c-4383-b415-262c81b43f75

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
theorem _root_.solution (l) : L.p l * L.Dri = L.Dri * (L.p l + algebraMap ℂ A (-1)) := by
  have h := ofFn_shift (L.p l) r L.ci (fun m => if l = m then -1 else 0) (fun m => by
    rw [L.p_ci]; split_ifs <;> simp [mul_add, sub_eq_add_neg])
  rw [show (∑ m : Fin r, if l = m then (-1:ℂ) else 0) = -1 by simp] at h
  exact h
end Formalism.FourierDecayAlt.P.RuleSS
