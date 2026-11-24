-- Prove2me | solution 1 for Formalism.G.LogP.evalYZero_atY
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:09:33.814513+00:00
-- url     : https://prove2.me/submissions/75c16afd-1e8d-4f0e-8c1d-5aceb11c4cf6

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_hb0
import Theorems.Thm_Formalism_G_LogP_hX1

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
    MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0] (atY φ) =
      PowerSeries.C (PowerSeries.constantCoeff φ) := by
  rw [atY, psubst_subst φ hX1 hb0, subst_X hb0]
  simp [PowerSeries.subst_zero_eq_C_constantCoeff]
  rfl
end Formalism.G.LogP
