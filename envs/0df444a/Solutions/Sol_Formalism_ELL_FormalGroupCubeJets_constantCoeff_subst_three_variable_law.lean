-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.constantCoeff_subst_three_variable_law
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:15:41.365829+00:00
-- url     : https://prove2.me/submissions/da2847d4-2fcf-4691-9e7f-1f3ce3795272

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_constantCoeff_three_variable_law
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero


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
theorem _root_.solution (ψ : PowerSeries K) :
    MvPowerSeries.constantCoeff (ψ.subst (F3 F)) = PowerSeries.constantCoeff ψ := by
  rw [PowerSeries.subst_def, constantCoeff_subst_of_zero _ (fun _ => constantCoeff_three_variable_law F)]
  rfl
end Formalism.ELL.FormalGroupCubeJets
