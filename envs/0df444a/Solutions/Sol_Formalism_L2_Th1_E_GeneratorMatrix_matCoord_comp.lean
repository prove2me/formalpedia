-- Prove2me | solution 1 for Formalism.L2.Th1.E.GeneratorMatrix.matCoord_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:36:30.775093+00:00
-- url     : https://prove2.me/submissions/e0dbb7d2-0a84-4cb4-8a2b-4a26a480e879

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementN
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_ConstantCoeffInVarEqZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_PhNormFromDatum
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Theorems.Thm_Formalism_L2_Th1_E_GeneratorMatrix_cc_matCoord
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_hs
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_sum_l
import Theorems.Thm_Formalism_L2_Th1_C_Pts_l_flin
import Theorems.Thm_Formalism_L2_Th1_C_Pts_substMv_subst


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
theorem _root_.solution (h : IsLogPair l linv) (τ : O →+* K) (γ δ : Matrix m m O) (w : m) :
    MvPowerSeries.subst (matCoord l linv τ δ) (matCoord l linv τ γ w) =
      matCoord l linv τ (γ * δ) w := by
  have hδ0 := cc_matCoord h τ δ
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero hδ0
  have hL : ∀ j, PowerSeries.subst (matCoord l linv τ δ j) l =
      ∑ k, MvPowerSeries.C (τ (δ j k)) *
        PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries m K) l := fun j =>
    Formalism.L2.Th1.C.Pts.l_flin h _ fun _ => MvPowerSeries.constantCoeff_X _
  conv_lhs => rw [matCoord, Formalism.L2.Th1.C.flin]
  rw [Formalism.L2.Th1.C.Pts.substMv_subst
    (Formalism.L2.Th1.C.Pts.constantCoeff_sum_l h _ fun _ => MvPowerSeries.constantCoeff_X _) hδ0]
  conv_rhs => rw [matCoord, Formalism.L2.Th1.C.flin]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom hs, map_sum]
  have h1 : ∀ j, MvPowerSeries.substAlgHom hs (MvPowerSeries.C (τ (γ w j)) *
      PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries m K) l) =
      ∑ k, MvPowerSeries.C (τ (γ w j * δ j k)) *
        PowerSeries.subst (MvPowerSeries.X k : MvPowerSeries m K) l := by
    intro j
    rw [map_mul, MvPowerSeries.coe_substAlgHom hs, MvPowerSeries.subst_C,
      Formalism.L2.Th1.C.Pts.substMv_subst (MvPowerSeries.constantCoeff_X j) hδ0,
      MvPowerSeries.subst_X hs, hL, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, mul_assoc]
  rw [Finset.sum_congr rfl fun j _ => h1 j, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply, map_sum, map_sum, Finset.sum_mul]
end Formalism.L2.Th1.E.GeneratorMatrix
