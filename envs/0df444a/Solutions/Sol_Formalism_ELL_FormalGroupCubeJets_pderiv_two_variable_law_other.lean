-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.pderiv_two_variable_law_other
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:02.515378+00:00
-- url     : https://prove2.me/submissions/8a1de4f5-d556-494d-bfb7-2882a0418722

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
import Theorems.Thm_Formalism_G_LogCR_pderiv_subst


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
theorem _root_.solution (a b k : Fin 3) (ha : a ≠ k) (hb : b ≠ k) :
    MvPowerSeries.pderiv K k (F2 F a b) = 0 := by
  rw [F2, pderiv_subst (fun i => by fin_cases i <;> simp [Y3])]
  simp [Fin.sum_univ_two, Y3, pderiv_X_of_ne ha, pderiv_X_of_ne hb]
end Formalism.ELL.FormalGroupCubeJets
