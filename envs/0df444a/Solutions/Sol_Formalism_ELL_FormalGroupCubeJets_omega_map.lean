-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.omega_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:16:50.400969+00:00
-- url     : https://prove2.me/submissions/76701575-083e-4ec0-badc-541cc04a57cd

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_pderiv_map
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_FK_eq
import Theorems.Thm_Formalism_G_LogP_hb0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.FormalGroupCubeJets
open MvPowerSeries Formalism.G Formalism.G.LogCR Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]
variable (F : FormalGroup (unitBall K))
namespace Formalism.ELL.FormalGroupCubeJets
theorem _root_.solution : omegaF F = PowerSeries.map (unitBall K).subtype
    (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries (unitBall K)), 0]
      (MvPowerSeries.pderiv (unitBall K) 1 F.toPowerSeries)) := by
  have hb : MvPowerSeries.HasSubst ![(PowerSeries.X : PowerSeries (unitBall K)), 0] := hb0
  rw [PowerSeries.map, MvPowerSeries.map_subst hb, ← pderiv_map, ← FK_eq, omegaF]
  congr 1
  funext i
  fin_cases i
  · simp [PowerSeries.X]
  · simp
end Formalism.ELL.FormalGroupCubeJets
