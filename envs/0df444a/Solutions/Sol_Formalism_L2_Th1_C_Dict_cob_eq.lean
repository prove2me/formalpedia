-- Prove2me | solution 1 for Formalism.L2.Th1.C.Dict.cob_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:22:08.723885+00:00
-- url     : https://prove2.me/submissions/a690201b-2bab-42e7-b144-f36e9fd5134e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_FirstLevelFromUniversal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_Points
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_SecondCoeffConsistency
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_ConstantCoeffVecConsPairEqZero

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
theorem _root_.solution (ph : PowerSeries K) :
    Formalism.InvariantFactorPaths.G7.cob (fadd l linv (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2))) ph =
      be0 l linv ph (MvPowerSeries.X (0 : Fin 2)) (MvPowerSeries.X (1 : Fin 2)) := rfl
end Formalism.L2.Th1.C.Dict
