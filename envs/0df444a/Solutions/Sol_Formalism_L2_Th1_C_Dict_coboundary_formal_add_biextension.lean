-- Prove2me | solution 1 for Formalism.L2.Th1.C.Dict.coboundary_formal_add_biextension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:51:09.584634+00:00
-- url     : https://prove2.me/submissions/a128765f-c2dd-4091-a26e-cdddb0a8190b

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Theorems.Thm_Formalism_L2_Th1_C_Dict_subst_cob
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_fadd
import Theorems.Thm_Formalism_L2_Th1_C_Pts_fadd_eq_substMv


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
theorem _root_.solution (h : IsLogPair l linv) (ph : PowerSeries K) :
    Formalism.InvariantFactorPaths.G7.d1 (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)))
      (Formalism.InvariantFactorPaths.G7.cob (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) ph) =
      be0 l linv ph (fadd l linv (MvPowerSeries.X (0 : Fin 3)) (MvPowerSeries.X (1 : Fin 3)))
          (MvPowerSeries.X (2 : Fin 3)) -
        be0 l linv ph (MvPowerSeries.X (0 : Fin 3)) (MvPowerSeries.X (2 : Fin 3)) -
        be0 l linv ph (MvPowerSeries.X (1 : Fin 3)) (MvPowerSeries.X (2 : Fin 3)) := by
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have h1 : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have h2 : MvPowerSeries.constantCoeff (MvPowerSeries.X (2 : Fin 3) : MvPowerSeries (Fin 3) K) = 0 :=
    MvPowerSeries.constantCoeff_X 2
  have e : Formalism.InvariantFactorPaths.G7.in3
      (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) =
      fadd l linv (MvPowerSeries.X (0 : Fin 3)) (MvPowerSeries.X (1 : Fin 3)) :=
    (Pts.fadd_eq_substMv h h0 h1).symm
  rw [Formalism.InvariantFactorPaths.G7.d1, e, subst_cob h ph (Pts.constantCoeff_fadd h h0 h1) h2, subst_cob h ph h0 h2,
    subst_cob h ph h1 h2]
end Formalism.L2.Th1.C.Dict
