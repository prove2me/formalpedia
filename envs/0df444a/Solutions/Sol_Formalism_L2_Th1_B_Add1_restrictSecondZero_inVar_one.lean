-- Prove2me | solution 1 for Formalism.L2.Th1.B.Add1.restrictSecondZero_inVar_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:21:25.243801+00:00
-- url     : https://prove2.me/submissions/8bc9083c-d2e3-49c4-b78c-490380b58f65

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ChainRule
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_RestrictSecondZeroInVarOne
import Theorems.Thm_Formalism_L2_Th1_B_Add1_triple_lintegral_eq
import Theorems.Thm_Formalism_L2_Th1_B_Add1_evalYZero_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.L2.Th1.B.Add1
open Formalism.InvariantFactorPaths.G7 (at1)
section SlopeTestRemainingChoices
variable {K : Type} [Field K] [CharZero K]
private theorem at1_mul {ι : Type} (x : ι) (f g : PowerSeries K) :
    Formalism.InvariantFactorPaths.G7.at1 x (f * g) = Formalism.InvariantFactorPaths.G7.at1 x f * Formalism.InvariantFactorPaths.G7.at1 x g := by
  simp only [triple_lintegral_eq, map_mul]
private theorem at1_X_eq_X {ι : Type} (x : ι) :
    Formalism.InvariantFactorPaths.G7.at1 x (PowerSeries.X : PowerSeries K) = MvPowerSeries.X x :=
  PowerSeries.subst_X (PowerSeries.HasSubst.X x)
private theorem ev0_mul (a b : MvPowerSeries (Fin 2) K) :
    Formalism.L2.Th1.B.ev0 (a * b) = Formalism.L2.Th1.B.ev0 a * Formalism.L2.Th1.B.ev0 b := by
  simp only [evalYZero_eq, map_mul]
private theorem ev0_X_one_eq_zero : Formalism.L2.Th1.B.ev0 (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
  rw [evalYZero_eq, ev0H, MvPowerSeries.substAlgHom_X]
  rfl
end SlopeTestRemainingChoices
end Formalism.L2.Th1.B.Add1
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.Add1
open Formalism.InvariantFactorPaths.G7 (at1)
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.B.Add1
theorem _root_.solution {f : PowerSeries K} (hf : PowerSeries.constantCoeff f = 0) :
    ev0 (at1 1 f) = 0 := by
  obtain ⟨g, rfl⟩ := PowerSeries.X_dvd_iff.mpr hf
  rw [at1_mul, at1_X_eq_X, ev0_mul, ev0_X_one_eq_zero, zero_mul]
end Formalism.L2.Th1.B.Add1
