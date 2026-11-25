-- Prove2me | solution 1 for Formalism.L2.Th1.E.GeneratorMatrix.tensor4_eq_rename
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:59:50.2138+00:00
-- url     : https://prove2.me/submissions/fe3ce71d-9eae-4736-9f7c-f13d4a384ce3

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq)
open Formalism.L2.Th1.C (IntMv IntPS IsPt IsLogPair)
open CompatibleChartOperations
open Formalism.L2.Th1.E.GeneratorMatrix
variable {K : Type} [Field K] {n : Type}
namespace Formalism.L2.Th1.E.GeneratorMatrix
theorem _root_.solution (f : MvPowerSeries n K) :
    tensor4 f = ∏ a, MvPowerSeries.rename (blk n a) f := by
  unfold tensor4
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [MvPowerSeries.rename_eq_subst]
  rfl
end Formalism.L2.Th1.E.GeneratorMatrix
