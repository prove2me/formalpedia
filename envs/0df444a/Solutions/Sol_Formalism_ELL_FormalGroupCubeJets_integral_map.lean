-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.integral_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:44:28.428786+00:00
-- url     : https://prove2.me/submissions/859ae26a-4ce9-4b5b-b2bf-fa8fd77a98d4

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube

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
namespace Formalism.ELL.FormalGroupCubeJets
theorem _root_.solution {σ : Type} (g : MvPowerSeries σ (unitBall K)) :
    IntegralMv (MvPowerSeries.map (unitBall K).subtype g) := by
  intro d
  rw [MvPowerSeries.coeff_map]
  exact (MvPowerSeries.coeff d g).2
end Formalism.ELL.FormalGroupCubeJets
