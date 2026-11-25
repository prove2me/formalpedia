-- Prove2me | solution 1 for Formalism.L2.Th1.E.fourth_power
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:51:10.629458+00:00
-- url     : https://prove2.me/submissions/d237e6e9-2ecc-48f2-832c-922b1d1f953d

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Theorems.Thm_Formalism_L2_Th1_E_GeneratorMatrix_coeff_tensor4

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
open GeneratorMatrix
namespace Formalism.L2.Th1.E
theorem _root_.solution : FourthPower := by
  intro K _ _ n f h ν
  have h1 := h (∑ a, Finsupp.embDomain (blk n a) ν)
  rw [coeff_tensor4, norm_pow] at h1
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h1
end Formalism.L2.Th1.E
