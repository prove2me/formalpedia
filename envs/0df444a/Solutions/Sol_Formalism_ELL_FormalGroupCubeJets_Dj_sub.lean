-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.Dj_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:41.577332+00:00
-- url     : https://prove2.me/submissions/f4d13cbf-7771-48b9-91ca-25bde9627898

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
variable (F : FormalGroup (unitBall K))
namespace Formalism.ELL.FormalGroupCubeJets
theorem _root_.solution (j : Fin 3) (a b : MvPowerSeries (Fin 3) K) : Dj F j (a - b) = Dj F j a - Dj F j b := by
  rw [Dj, Dj, Dj, map_sub, mul_sub]
end Formalism.ELL.FormalGroupCubeJets
