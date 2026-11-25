-- Prove2me | solution 1 for Formalism.L2.Th1.H.FormalGroupLawNegation.left_side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:47:30.349673+00:00
-- url     : https://prove2.me/submissions/96095fdd-f818-4195-8bd2-50470b78d7b9

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_QuadraticSemicharactersFactVersion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_GeneralIntegrality
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_SubstSingleVar
import Theorems.Thm_Formalism_L2_Th1_H_FormalGroupLawNegation_cc_lin
import Theorems.Thm_Formalism_L2_Th1_H_FormalGroupLawNegation_subst_lin
import Theorems.Thm_Formalism_L2_Th1_H_FormalGroupLawNegation_subst_tensor4
import Theorems.Thm_Formalism_L2_Th1_H_FormalGroupLawNegation_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_single_var
import Theorems.Thm_Formalism_L2_Th1_C_Clo_CoeffCont_subst
import Theorems.Thm_Formalism_L2_Th1_C_Pts_constantCoeff_flin
import Theorems.Thm_Formalism_L2_Th1_C_Pts_l_flin
import Theorems.Thm_Formalism_L2_Th1_E_CompatibleChartOperations_constantCoeff_inVar_eq_zero
import Theorems.Thm_Formalism_LT_LTL_cc_lin


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (at1)
open Formalism.L2.Th1.C (IsLogPair)
open Formalism.L2.Th1.E (tensor4 matCoord thetaProd)
open Formalism.L2.Th1.H.FormalGroupLawNegation
variable {K : Type} [Field K] {n : Type} [Fintype n]
namespace Formalism.L2.Th1.H.FormalGroupLawNegation
theorem _root_.solution {lg linv : PowerSeries K} (h : IsLogPair lg linv) {O : Type} [Semiring O] (τ : O →+* K)
    (γ : Matrix (Fin 4 × n) (Fin 4 × n) O) (B' : Matrix n n K) (M : Matrix (Fin 4 × n) (Fin 4 × n) K)
    (hM : ∀ (a : Fin 4) (i : n) (w : Fin 4 × n), ∑ j, B' i j * τ (γ (a, j) w) = M (a, i) w)
    (T : MvPowerSeries n K) :
    MvPowerSeries.subst (matCoord lg linv τ γ)
        (tensor4 (MvPowerSeries.subst (fun i => ∑ j, MvPowerSeries.C (B' i j) * at1 j lg) T)) =
      MvPowerSeries.subst (fun w => at1 w lg) (linSubst M (tensor4 T)) := by
  have hat : ∀ {σ : Type} (s : σ), MvPowerSeries.constantCoeff (at1 s lg : MvPowerSeries σ K) = 0 :=
    fun s => Formalism.L2.Th1.E.CompatibleChartOperations.constantCoeff_inVar_eq_zero s h.1
  have hmc : ∀ w, MvPowerSeries.constantCoeff (matCoord lg linv τ γ w) = 0 := fun w =>
    Formalism.L2.Th1.C.Pts.constantCoeff_flin h _ fun _ => MvPowerSeries.constantCoeff_X _
  have hB : ∀ i, MvPowerSeries.constantCoeff
      (∑ j, MvPowerSeries.C (B' i j) * (at1 j lg : MvPowerSeries n K)) = 0 :=
    fun i => cc_lin _ fun j => hat j
  have hL : ∀ w, MvPowerSeries.constantCoeff
      (∑ w', MvPowerSeries.C (M w w') * (MvPowerSeries.X w' : MvPowerSeries (Fin 4 × n) K)) = 0 :=
    fun w => cc_lin _ fun j => MvPowerSeries.constantCoeff_X _
  rw [subst_tensor4 _ hmc, linSubst, subst_tensor4 _ hL,
    ← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero fun w => hat w), map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [MvPowerSeries.coe_substAlgHom,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hB)
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => hmc (a, i)),
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => hL (a, i))
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun w => hat w)]
  congr 1
  funext i
  rw [subst_lin _ _ fun j => hmc (a, j), subst_lin _ _ fun w => hat w]
  have h1 : ∀ j, MvPowerSeries.subst (fun i => matCoord lg linv τ γ (a, i)) (at1 j lg) =
      ∑ w, MvPowerSeries.C (τ (γ (a, j) w)) * at1 w lg := by
    intro j
    rw [subst_single_var _ _ fun j => hmc (a, j)]
    exact Formalism.L2.Th1.C.Pts.l_flin h _ fun _ => MvPowerSeries.constantCoeff_X _
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero fun w => hat w), ← hM, map_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, mul_assoc]
end Formalism.L2.Th1.H.FormalGroupLawNegation
