-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.integral_omegaX
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:22:57.351527+00:00
-- url     : https://prove2.me/submissions/4112b652-8e78-43a1-9a8e-0f7c7b7f91dd

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_integral_map
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_omega_map

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
theorem _root_.solution (j : Fin 3) :
    IntegralMv ((omegaF F).subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K)) := by
  have hX : PowerSeries.HasSubst (MvPowerSeries.X j : MvPowerSeries (Fin 3) (unitBall K)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  have : (omegaF F).subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) =
      MvPowerSeries.map (unitBall K).subtype
        (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) (unitBall K))
          (MvPowerSeries.subst ![(PowerSeries.X : PowerSeries (unitBall K)), 0]
          (MvPowerSeries.pderiv (unitBall K) 1 F.toPowerSeries) : PowerSeries (unitBall K))) := by
    rw [PowerSeries.map_subst hX, MvPowerSeries.map_X, ← omega_map]
  rw [this]
  exact integral_map _
end Formalism.ELL.FormalGroupCubeJets
