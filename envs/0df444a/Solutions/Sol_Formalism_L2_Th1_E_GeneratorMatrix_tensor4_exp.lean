-- Prove2me | solution 1 for Formalism.L2.Th1.E.GeneratorMatrix.tensor4_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:43:54.698799+00:00
-- url     : https://prove2.me/submissions/ef33b764-20ab-47b1-9825-a8cf897cfb1e

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_IntegralMvPolynomialLemmas_substMv_mvExp
import Theorems.Thm_Formalism_L2_Th1_C_mvExp_sum
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_cc_phSum
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_constantCoeff_inVar_eq_zero
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_subst_phSum


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
variable {K : Type} [NormedField K] [CharZero K] {n : Type} [Fintype n]
namespace Formalism.L2.Th1.E.GeneratorMatrix
theorem _root_.solution {ph : PowerSeries K} (hph : PowerSeries.constantCoeff ph = 0) :
    tensor4 (mvExp (phSum ph : MvPowerSeries n K)) =
      mvExp (phSum ph : MvPowerSeries (Fin 4 × n) K) := by
  have h1 : ∀ a : Fin 4, MvPowerSeries.subst
      (fun i => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K))
      (mvExp (phSum ph : MvPowerSeries n K)) = mvExp (∑ i, at1 (a, i) ph) := by
    intro a
    have h0 : ∀ i : n, MvPowerSeries.constantCoeff
        (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K) = 0 :=
      fun i => MvPowerSeries.constantCoeff_X _
    have h2 : MvPowerSeries.subst (fun i => (MvPowerSeries.X (a, i) : MvPowerSeries (Fin 4 × n) K))
        (phSum ph : MvPowerSeries n K) = ∑ i, at1 (a, i) ph := subst_phSum ph h0
    rw [← h2]
    exact Formalism.L2.Th1.C.IntegralMvPolynomialLemmas.substMv_mvExp (cc_phSum hph) h0
  unfold tensor4
  rw [Finset.prod_congr rfl fun a _ => h1 a]
  have h3 : (phSum ph : MvPowerSeries (Fin 4 × n) K) = ∑ a : Fin 4, ∑ i : n, at1 (a, i) ph := by
    unfold phSum
    exact Fintype.sum_prod_type _
  rw [h3]
  refine (Formalism.L2.Th1.C.mvExp_sum _ _ fun a _ => ?_).symm
  rw [map_sum]
  exact Finset.sum_eq_zero fun i _ => constantCoeff_inVar_eq_zero _ hph
end Formalism.L2.Th1.E.GeneratorMatrix
