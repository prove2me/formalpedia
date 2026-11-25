-- Prove2me | solution 1 for Formalism.L2.Th1.E.GeneratorMatrix.cc_matCoord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:54:17.297193+00:00
-- url     : https://prove2.me/submissions/6a5a87f5-3e13-45de-8b7e-4391622de5af

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_flin


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
theorem _root_.solution (h : IsLogPair l linv) (τ : O →+* K) (γ : Matrix m m O) (w : m) :
    MvPowerSeries.constantCoeff (matCoord l linv τ γ w) = 0 :=
  Formalism.L2.Th1.C.Pts.constantCoeff_flin h _ fun _ => MvPowerSeries.constantCoeff_X _
end Formalism.L2.Th1.E.GeneratorMatrix
