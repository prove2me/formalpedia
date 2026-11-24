-- Prove2me | solution 1 for Formalism.G.LogP.pderiv_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:28.136272+00:00
-- url     : https://prove2.me/submissions/e51e6eab-ad04-480e-85c3-388814792b72

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Theorems.Thm_Formalism_G_LogP_hX0
import Theorems.Thm_Formalism_G_LogP_hX1
import Theorems.Thm_Formalism_G_LogCR_pderiv_psubst


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
    (PowerSeries.derivative R g).subst F.toPowerSeries * MvPowerSeries.pderiv R 1 F.toPowerSeries =
      atY (PowerSeries.derivative R g) := by
  have := congrArg (MvPowerSeries.pderiv R 1) hg.2.2
  rw [pderiv_psubst F.zero_constantCoeff, map_add, atX, atY, pderiv_psubst hX0,
    pderiv_psubst hX1] at this
  simpa [pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)] using this
end Formalism.G.LogP
