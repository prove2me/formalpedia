-- Prove2me | solution 1 for Formalism.ELL.FormalGroupCubeJets.step2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:23:14.096936+00:00
-- url     : https://prove2.me/submissions/66c7665b-84f5-4845-8c44-f9f4743c718b

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsCube
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_Dj_sub
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_Dj_add
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_Dj_C
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_Dj_const
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_Dj_X
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_rti
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_ccX
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_constantCoeff_two_variable_law
import Theorems.Thm_Formalism_ELL_FormalGroupCubeJets_pderiv_two_variable_law_other

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
theorem _root_.solution (φ : PowerSeries K) : Dj F 2 (triDiff F φ) =
    (invD F φ).subst (F3 F) - (invD F φ).subst (F2 F 0 2) - (invD F φ).subst (F2 F 1 2)
      + (invD F φ).subst (Y3 2) := by
  have h3 : Dj F 2 (φ.subst (F3 F)) = (invD F φ).subst (F3 F) :=
    rti F φ (constantCoeff_two_variable_law F 0 1) 2 (pderiv_two_variable_law_other F 0 1 2 (by decide) (by decide))
  have h01 : Dj F 2 (φ.subst (F2 F 0 1)) = 0 :=
    Dj_const F 2 φ (constantCoeff_two_variable_law F 0 1) (pderiv_two_variable_law_other F 0 1 2 (by decide) (by decide))
  have h02 : Dj F 2 (φ.subst (F2 F 0 2)) = (invD F φ).subst (F2 F 0 2) :=
    rti F φ (ccX 0) 2 (pderiv_X_of_ne (by decide))
  have h12 : Dj F 2 (φ.subst (F2 F 1 2)) = (invD F φ).subst (F2 F 1 2) :=
    rti F φ (ccX 1) 2 (pderiv_X_of_ne (by decide))
  have hx0 : Dj F 2 (φ.subst (Y3 0 : MvPowerSeries (Fin 3) K)) = 0 :=
    Dj_const F 2 φ (ccX 0) (pderiv_X_of_ne (by decide))
  have hx1 : Dj F 2 (φ.subst (Y3 1 : MvPowerSeries (Fin 3) K)) = 0 :=
    Dj_const F 2 φ (ccX 1) (pderiv_X_of_ne (by decide))
  have hx2 : Dj F 2 (φ.subst (Y3 2 : MvPowerSeries (Fin 3) K)) =
      (invD F φ).subst (Y3 2 : MvPowerSeries (Fin 3) K) := Dj_X F 2 φ
  rw [triDiff]
  simp only [Dj_sub, Dj_add, Dj_C, h3, h01, h02, h12, hx0, hx1, hx2]
  ring
end Formalism.ELL.FormalGroupCubeJets
