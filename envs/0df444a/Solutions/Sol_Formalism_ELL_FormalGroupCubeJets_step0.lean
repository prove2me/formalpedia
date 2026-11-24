-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.step0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:38:48.824798+00:00
-- url     : https://prove2.me/submissions/4b8bcefe-37c0-4594-9875-d8d28e5a09fe

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_Dj_sub
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_Dj_const
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_constantCoeff_two_variable_law
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_pderiv_two_variable_law_other
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_pderiv_zero_subst_three_variable_law

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
theorem _root_.solution (φ : PowerSeries K) : Dj F 0
    ((invD F (invD F φ)).subst (F3 F) - (invD F (invD F φ)).subst (F2 F 1 2)) =
    (invD F (invD F (invD F φ))).subst (F3 F) := by
  have h12 : Dj F 0 ((invD F (invD F φ)).subst (F2 F 1 2)) = 0 :=
    Dj_const F 0 _ (constantCoeff_two_variable_law F 1 2) (pderiv_two_variable_law_other F 1 2 0 (by decide) (by decide))
  rw [Dj_sub, pderiv_zero_subst_three_variable_law, h12, sub_zero]
end Formalism.ELL.FormalGroupCubeJets
