-- Prove2me | solution 1 for Formalism.G.LogP.derivative_log_mul_omega
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:15.126235+00:00
-- url     : https://prove2.me/submissions/14a746d8-a4da-4c73-97a4-0def30883130

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Theorems.Thm_Formalism_G_LogP_hb0
import Theorems.Thm_Formalism_G_LogP_eval_zero_subst_law
import Theorems.Thm_Formalism_G_LogP_evalYZero_atY
import Theorems.Thm_Formalism_G_LogP_pderiv_log

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
theorem _root_.solution {g : PowerSeries R} (hg : IsLog F g) :
    PowerSeries.derivative R g * omegaF F = 1 := by
  have := congrArg (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries R), 0]) (pderiv_log F hg)
  rw [subst_mul hb0, eval_zero_subst_law, evalYZero_atY] at this
  rw [omegaF, this]
  have h1 : PowerSeries.constantCoeff (PowerSeries.derivative R g) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative, hg.2.1]
    simp
  rw [h1, map_one]
end Formalism.G.LogP
