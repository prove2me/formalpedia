-- Prove2me | solution 1 for Formalism.L2.Th1.C.Dict.law_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:30:29.626958+00:00
-- url     : https://prove2.me/submissions/c568b925-2815-4016-ac7e-04fff0b29d6b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Theorems.Thm_Formalism_L2_Th1_C_Pts_subst_linv_l


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
variable {K : Type} [Field K] {σ τ : Type} {l linv : PowerSeries K}
namespace Formalism.L2.Th1.C.Dict
theorem _root_.solution (h : IsLogPair l linv) {F : MvPowerSeries (Fin 2) K}
    (hF : MvPowerSeries.constantCoeff F = 0) (hc : Formalism.InvariantFactorPaths.G7.cob F l = 0) :
    F = fadd l linv (MvPowerSeries.X 0) (MvPowerSeries.X 1) := by
  have e : PowerSeries.subst F l = PowerSeries.subst (MvPowerSeries.X (0 : Fin 2)) l +
      PowerSeries.subst (MvPowerSeries.X (1 : Fin 2)) l := by
    have := hc
    rw [Formalism.InvariantFactorPaths.G7.cob, Formalism.InvariantFactorPaths.G7.at1, Formalism.InvariantFactorPaths.G7.at1] at this
    linear_combination this
  rw [fadd, ← e, Pts.subst_linv_l h hF]
end Formalism.L2.Th1.C.Dict
