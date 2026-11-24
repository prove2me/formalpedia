-- Prove2me | solution 1 for Formalism.G.LogP.log_unique
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:46.013043+00:00
-- url     : https://prove2.me/submissions/d01fcf11-fb7f-4855-a25f-d61a82892680

import Definitions.Def_Formalism_FormalGroupLog_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Theorems.Thm_Formalism_G_LogP_isUnit_natCast_succ
import Theorems.Thm_Formalism_G_LogP_constantCoeff_omega
import Theorems.Thm_Formalism_G_LogP_derivative_log_mul_omega

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPowerSeries
open Formalism Formalism.G Formalism.G.LogP
open Formalism.G.LogCR
variable {R : Type*} [CommRing R]
variable (F : FormalGroup R)
namespace Formalism.G.LogP
theorem _root_.solution [Algebra ℚ R] {f g : PowerSeries R} (hf : IsLog F f) (hg : IsLog F g) :
    f = g := by
  have hd : PowerSeries.derivative R f = PowerSeries.derivative R g := by
    have hu := PowerSeries.mul_invOfUnit (omegaF F) 1 (by simp [constantCoeff_omega])
    calc PowerSeries.derivative R f
        = PowerSeries.derivative R f * omegaF F * PowerSeries.invOfUnit (omegaF F) 1 := by
          rw [mul_assoc, hu, mul_one]
      _ = PowerSeries.derivative R g * omegaF F * PowerSeries.invOfUnit (omegaF F) 1 := by
          rw [derivative_log_mul_omega F hf, derivative_log_mul_omega F hg]
      _ = PowerSeries.derivative R g := by rw [mul_assoc, hu, mul_one]
  ext n
  cases n with
  | zero => simpa using hf.1.trans hg.1.symm
  | succ n =>
    have := congrArg (PowerSeries.coeff n) hd
    rw [PowerSeries.coeff_derivative, PowerSeries.coeff_derivative] at this
    exact (isUnit_natCast_succ (R := R) n).mul_left_cancel (by
      rw [mul_comm, this, mul_comm])
end Formalism.G.LogP
