-- Prove2me | solution 1 for Formalism.L2.Th1.E.GeneratorMatrix.blk_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:55:32.643281+00:00
-- url     : https://prove2.me/submissions/d72346d4-1419-4781-a611-954c26fcb86e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_inj
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst


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
namespace Formalism.L2.Th1.E.GeneratorMatrix
theorem _root_.solution {n : Type} (a b : Fin 4) (μ : n →₀ ℕ) (i : n) :
    Finsupp.embDomain (blk n a) μ (b, i) = if a = b then μ i else 0 := by
  split_ifs with h
  · subst h
    exact Finsupp.embDomain_apply_self (blk n a) μ i
  · refine Finsupp.embDomain_of_notMem_range _ _ _ ?_
    rintro ⟨j, hj⟩
    exact h (Prod.mk.inj hj).1
end Formalism.L2.Th1.E.GeneratorMatrix
