-- Prove2me | solution 1 for Formalism.ELL.FormalGroupLinearJets.coeff_one_subst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:19:51.464125+00:00
-- url     : https://prove2.me/submissions/16a5c7ca-0594-4463-a277-fc9efc76cbe3

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsOne
import Theorems.Thm_Formalism_ELL_FormalGroupLinearJets_constantCoeff_pderiv_unit
import Theorems.Thm_Formalism_G_LogCR_pderiv_psubst
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
open Formalism Formalism.ELL Formalism.ELL.FormalGroupLinearJets
variable {K : Type u} [CommRing K]
namespace Formalism.ELL.FormalGroupLinearJets
theorem _root_.solution {φ a : PowerSeries K} (ha : constantCoeff a = 0) :
    coeff 1 (φ.subst a) = coeff 1 φ * coeff 1 a := by
  have h := Formalism.G.LogCR.pderiv_psubst (τ := Unit) (a := (a : MvPowerSeries Unit K)) ha φ ()
  have h2 := congrArg MvPowerSeries.constantCoeff h
  rw [constantCoeff_pderiv_unit, map_mul, constantCoeff_pderiv_unit] at h2
  rw [h2]
  congr 1
  rw [PowerSeries.subst_def,
    Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) (τ := Unit) _ (fun _ => ha)]
  show PowerSeries.constantCoeff (PowerSeries.derivative K φ) = _
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
  simp
end Formalism.ELL.FormalGroupLinearJets
