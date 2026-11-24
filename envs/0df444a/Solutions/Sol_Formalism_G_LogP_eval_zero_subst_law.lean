-- Prove2me | solution 1 for Formalism.G.LogP.eval_zero_subst_law
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:34.126304+00:00
-- url     : https://prove2.me/submissions/0f3d6e12-0349-47f5-8342-73ca72df8a50

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_hb0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]
variable (F : FormalGroup R)
namespace Formalism.G.LogP
theorem _root_.solution (φ : PowerSeries R) :
    MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0] (φ.subst F.toPowerSeries) = φ := by
  rw [psubst_subst φ F.zero_constantCoeff hb0]
  have : MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0] F.toPowerSeries =
      PowerSeries.X := F.Xzero_eq_X
  rw [this, PowerSeries.X_subst]
end Formalism.G.LogP
