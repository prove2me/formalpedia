-- Prove2me | solution 1 for Formalism.L2.Th1.C.Dict.sgStar_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:33:49.780783+00:00
-- url     : https://prove2.me/submissions/f49bfac5-e259-40dc-ad21-5c1962034ed4

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Theorems.Thm_Formalism_L2_Th1_C_Dict_prim_prim
import Theorems.Thm_Formalism_L2_Th1_B_Ph_constantCoeff_sigS
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.Dict
variable {K : Type} [Field K] [CharZero K]
namespace Formalism.L2.Th1.C.Dict
theorem _root_.solution (e : PowerSeries K) (s2 : K) : Formalism.L2.Th1.B.sgStar s2 e = sgStar e s2 := by
  have h1 : MvPowerSeries.constantCoeff (-(dblInt e) : PowerSeries K) = 0 := by
    rw [← prim_prim]
    exact Formalism.L2.Th1.B.Ph.constantCoeff_sigS e
  have h2 : MvPowerSeries.constantCoeff
      (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2) : PowerSeries K) = 0 := by
    show PowerSeries.constantCoeff (-(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2)) = 0
    simp
  have e1 : -(lam e s2) = -(dblInt e) + -(PowerSeries.C (s2 / 2) * PowerSeries.X ^ 2) := by
    rw [lam]; ring
  rw [sgStar, e1, mvExp_add h1 h2, Formalism.L2.Th1.B.sgStar, Formalism.L2.Th1.B.sigma, Formalism.L2.Th1.B.sigS,
    prim_prim, mul_assoc]
  rfl
end Formalism.L2.Th1.C.Dict
