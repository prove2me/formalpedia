-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.step1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:37:06.631651+00:00
-- url     : https://prove2.me/submissions/d8c11fca-64ed-46d2-a408-642cb38f2cec

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_Dj_sub
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_Dj_add
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_Dj_const
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_rti
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_ccX
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_constantCoeff_two_variable_law
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_pderiv_two_variable_law_other
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_three_variable_law_eq_subst_second
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_two_variable_law_one_two_eq

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
theorem _root_.solution (φ : PowerSeries K) : Dj F 1
    ((invD F φ).subst (F3 F) - (invD F φ).subst (F2 F 0 2) - (invD F φ).subst (F2 F 1 2)
      + (invD F φ).subst (Y3 2)) =
    (invD F (invD F φ)).subst (F3 F) - (invD F (invD F φ)).subst (F2 F 1 2) := by
  have h3 : Dj F 1 ((invD F φ).subst (F3 F)) = (invD F (invD F φ)).subst (F3 F) := by
    rw [three_variable_law_eq_subst_second]
    exact rti F _ (constantCoeff_two_variable_law F 0 2) 1 (pderiv_two_variable_law_other F 0 2 1 (by decide) (by decide))
  have h02 : Dj F 1 ((invD F φ).subst (F2 F 0 2)) = 0 :=
    Dj_const F 1 _ (constantCoeff_two_variable_law F 0 2) (pderiv_two_variable_law_other F 0 2 1 (by decide) (by decide))
  have h12 : Dj F 1 ((invD F φ).subst (F2 F 1 2)) = (invD F (invD F φ)).subst (F2 F 1 2) := by
    rw [two_variable_law_one_two_eq]
    exact rti F _ (ccX 2) 1 (pderiv_X_of_ne (by decide))
  have hx2 : Dj F 1 ((invD F φ).subst (Y3 2 : MvPowerSeries (Fin 3) K)) = 0 :=
    Dj_const F 1 _ (ccX 2) (pderiv_X_of_ne (by decide))
  simp only [Dj_sub, Dj_add, h3, h02, h12, hx2]
  ring
end Formalism.ELL.FormalGroupCubeJets
