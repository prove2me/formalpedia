-- Prove2me | solution 1 for Formalism.ELL.jetsOne_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:49.548146+00:00
-- url     : https://prove2.me/submissions/95243538-16fa-4aed-ad3f-5dae3353a32d

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsOne
import Theorems.Thm_Formalism_ELL_FormalGroupLinearJets_constantCoeff_pderiv_unit
import Theorems.Thm_Formalism_ELL_FormalGroupLinearJets_coeff_one_subst
import Theorems.Thm_Formalism_G_LogP_constantCoeff_omega


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
open Formalism Formalism.ELL
open Formalism.G Formalism.ELL.FormalGroupLinearJets
namespace Formalism.ELL
theorem _root_.solution (hN : Formalism.ELL.NPderiv.{u}) : Formalism.ELL.JetsOne.{u} := by
  intro K _ _ _ F φ a n ha hG
  have hP := hN K Unit _ hG ()
  have h0 := hP 0
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_pderiv_unit, map_sub,
    coeff_one_subst ha.1, map_smul, smul_eq_mul] at h0
  have hD : constantCoeff (invD F φ) = coeff 1 φ := by
    have hw : constantCoeff (omegaF F) = 1 := Formalism.G.LogP.constantCoeff_omega (FK F)
    rw [invD, map_mul, hw, one_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_derivative]
    simp
  rw [hD]
  convert h0 using 2
  ring
end Formalism.ELL
