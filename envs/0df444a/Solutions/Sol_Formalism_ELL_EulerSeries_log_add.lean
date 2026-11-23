-- Prove2me | solution 1 for Formalism.ELL.EulerSeries.log_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:23:09.772349+00:00
-- url     : https://prove2.me/submissions/fd588f9a-3a5d-4170-93f3-5851809b2b7e

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_ConstantCoeffLogOnePlus
import Theorems.Thm_Formalism_ELL_EulerSeries_eul_apply
import Theorems.Thm_Formalism_ELL_EulerSeries_eq_zero_of_eulFun
import Theorems.Thm_Formalism_ELL_EulerSeries_eul_log_mul
import Theorems.Thm_Formalism_ELL_EulerSeries_constantCoeff_logOnePlus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.EulerSeries
open Formalism.G Formalism.ELL
variable {K : Type*} [NormedField K] [CharZero K] {σ : Type} [DecidableEq σ]
namespace Formalism.ELL.EulerSeries
theorem _root_.solution {f g : MvPowerSeries σ K} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    logOnePlus f + logOnePlus g = logOnePlus (f + g + f * g) := by
  have hh : MvPowerSeries.constantCoeff (f + g + f * g) = 0 := by
    simp only [map_add, map_mul, hf, hg, add_zero, mul_zero]
  have hu : IsUnit (1 + (f + g + f * g)) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, map_add, hh, map_one, add_zero]
    exact isUnit_one
  have e1 := eul_log_mul hf
  have e2 := eul_log_mul hg
  have e3 := eul_log_mul hh
  have hD : eulFun (f + g + f * g) = eulFun f + eulFun g + (f * eulFun g + g * eulFun f) := by
    show eul (f + g + f * g) = eul f + eul g + (f * eul g + g * eul f)
    rw [map_add, map_add, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  have key : eulFun (logOnePlus f + logOnePlus g - logOnePlus (f + g + f * g)) = 0 := by
    rw [← hu.mul_left_inj, zero_mul]
    show eul (logOnePlus f + logOnePlus g - logOnePlus (f + g + f * g)) * _ = 0
    rw [map_sub, map_add, eul_apply, eul_apply, eul_apply]
    linear_combination (1 + g) * e1 + (1 + f) * e2 - e3 - hD
  have := eq_zero_of_eulFun _ (by
    rw [map_sub, map_add, constantCoeff_logOnePlus hf, constantCoeff_logOnePlus hg,
      constantCoeff_logOnePlus hh, add_zero, sub_zero]) key
  exact sub_eq_zero.mp this
end Formalism.ELL.EulerSeries
