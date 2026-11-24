-- Prove2me | solution 1 for Formalism.L2.Th1.C.Dict.subst_cob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:35:22.310441+00:00
-- url     : https://prove2.me/submissions/a65de6db-4132-44cc-a8aa-27fcf2be0d9a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero
import Theorems.Thm_Formalism_L2_Th1_C_Dict_subst_biextension_form
import Theorems.Thm_Formalism_L2_Th1_C_Dict_constantCoeff_vecCons_pair_eq_zero
import Theorems.Thm_Formalism_L2_Th1_C_Dict_cob_eq

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
theorem _root_.solution (h : IsLogPair l linv) (ph : PowerSeries K) {x y : MvPowerSeries τ K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.subst ![x, y]
      (Formalism.InvariantFactorPaths.G7.cob (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) ph) =
      be0 l linv ph x y := by
  rw [cob_eq, subst_biextension_form h ph (MvPowerSeries.constantCoeff_X 0) (MvPowerSeries.constantCoeff_X 1)
      (constantCoeff_vecCons_pair_eq_zero hx hy),
    MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_vecCons_pair_eq_zero hx hy)),
    MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_vecCons_pair_eq_zero hx hy))]
  rfl
end Formalism.L2.Th1.C.Dict
