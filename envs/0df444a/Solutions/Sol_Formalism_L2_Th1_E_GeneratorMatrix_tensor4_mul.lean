-- Prove2me | solution 1 for Formalism.L2.Th1.E.GeneratorMatrix.tensor4_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:41:44.146833+00:00
-- url     : https://prove2.me/submissions/b1d04d47-0e19-46a7-953a-5e5a953a2a75

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Theorems.Thm_Formalism_L2_Th1_E_GeneratorMatrix_tensor4_eq_rename

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
theorem _root_.solution (f g : MvPowerSeries n K) : tensor4 (f * g) = tensor4 f * tensor4 g := by
  rw [tensor4_eq_rename, tensor4_eq_rename, tensor4_eq_rename, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun a _ => map_mul _ _ _
end Formalism.L2.Th1.E.GeneratorMatrix
