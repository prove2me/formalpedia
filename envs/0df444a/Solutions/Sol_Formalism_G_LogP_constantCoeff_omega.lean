-- Prove2me | solution 1 for Formalism.G.LogP.constantCoeff_omega
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:57:42.279746+00:00
-- url     : https://prove2.me/submissions/82b4f162-db7d-4001-9369-98e79d5fa39f

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero

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
theorem _root_.solution : PowerSeries.constantCoeff (omegaF F) = 1 := by
  have := constantCoeff_subst_of_zero (MvPowerSeries.pderiv R 1 F.toPowerSeries)
    (b := ![(PowerSeries.X : PowerSeries R), 0]) (fun i => by fin_cases i <;> simp [PowerSeries.X])
  rw [omegaF, PowerSeries.constantCoeff, this, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
  simpa using F.lin_coeff_Y
end Formalism.G.LogP
