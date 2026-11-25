-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.AltInv.intC_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:49:12.464018+00:00
-- url     : https://prove2.me/submissions/f825e1c2-89f7-45f6-b175-365e23c710a1

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_mul
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_intCast
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}
variable {σ τ : Type*}
namespace Formalism.L2.FormalSeriesBounds.AltInv
theorem _root_.solution {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n C) (hA : ∀ i j, IntC v (A i j)) :
    IntC v A.det := by
  rw [Matrix.det_apply]
  refine intC_sum _ fun s _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  exact intC_mul (intC_intCast _) (intC_prod _ fun i _ => hA _ _)
end Formalism.L2.FormalSeriesBounds.AltInv
