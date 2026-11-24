-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.Dj_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:23.954484+00:00
-- url     : https://prove2.me/submissions/6a4e020b-7f31-43b3-9006-8474ca15a056

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
theorem _root_.solution (j : Fin 3) (ψ : PowerSeries K) :
    Dj F j (ψ.subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K)) =
      (invD F ψ).subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) := by
  have hX : MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) = 0 := by simp
  rw [Dj, pderiv_psubst hX, pderiv_X_self, mul_one, invD,
    PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero hX)]
end Formalism.ELL.FormalGroupCubeJets
