-- Prove2me | solution 1 for Formalism.L2.Th1.E.GeneratorMatrix.matCoord_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:10:20.133123+00:00
-- url     : https://prove2.me/submissions/a0d69f1c-e4d7-4081-ba47-a440a380b0f7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
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
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1 Simeq)
open Formalism.L2.Th1.C (IntMv IntPS IsPt IsLogPair)
open CompatibleChartOperations
open Formalism.L2.Th1.E.GeneratorMatrix
variable {K : Type} [Field K] {O m : Type} [CommRing O] [Fintype m] {l linv : PowerSeries K}
namespace Formalism.L2.Th1.E.GeneratorMatrix
theorem _root_.solution [DecidableEq m] (h : IsLogPair l linv) (τ : O →+* K) (w : m) :
    matCoord l linv τ (1 : Matrix m m O) w = MvPowerSeries.X w := by
  rw [matCoord, Formalism.L2.Th1.C.flin, Finset.sum_eq_single w]
  · rw [Matrix.one_apply_eq, map_one, map_one, one_mul]
    exact Formalism.L2.Th1.C.Pts.subst_linv_l h (MvPowerSeries.constantCoeff_X w)
  · intro j _ hj
    rw [Matrix.one_apply_ne hj.symm, map_zero, map_zero, zero_mul]
  · intro hw
    exact absurd (Finset.mem_univ w) hw
end Formalism.L2.Th1.E.GeneratorMatrix
