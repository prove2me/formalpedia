-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.integral_Dj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:25:20.582452+00:00
-- url     : https://prove2.me/submissions/564760f5-b41a-4bdf-94f5-6d175faacd8a

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_integral_mul
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_integral_pderiv
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_integral_omegaX

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
theorem _root_.solution (j : Fin 3) {g : MvPowerSeries (Fin 3) K} (hg : IntegralMv g) :
    IntegralMv (Dj F j g) :=
  integral_mul (integral_omegaX F j) (integral_pderiv j hg)
end Formalism.ELL.FormalGroupCubeJets
