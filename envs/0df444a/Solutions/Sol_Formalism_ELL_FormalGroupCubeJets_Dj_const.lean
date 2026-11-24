-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.Dj_const
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:50.538917+00:00
-- url     : https://prove2.me/submissions/e87f0baa-57a2-4a7c-9e27-134dc321296e

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
import Theorems.Thm_Formalism_G_LogCR_pderiv_psubst


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
theorem _root_.solution (j : Fin 3) (ψ : PowerSeries K) {A : MvPowerSeries (Fin 3) K}
    (hA : MvPowerSeries.constantCoeff A = 0) (hdA : MvPowerSeries.pderiv K j A = 0) :
    Dj F j (ψ.subst A) = 0 := by
  rw [Dj, pderiv_psubst hA, hdA, mul_zero, mul_zero]
end Formalism.ELL.FormalGroupCubeJets
