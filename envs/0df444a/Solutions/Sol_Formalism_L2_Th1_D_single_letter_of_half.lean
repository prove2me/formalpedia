-- Prove2me | solution 1 for Formalism.L2.Th1.D.single_letter_of_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:26:40.963572+00:00
-- url     : https://prove2.me/submissions/d160b696-1eb3-4f36-9d45-b697779300ea

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionPointsIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_IpNormPowSubPowLe
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_ExponentialSpecification
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_BiextensionHypothesesOfConditions
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_AtVariableArtinHasseEqOneLog
import Theorems.Thm_Formalism_L2_Th1_D_SingleLetterLog_at_variable_artin_hasse_eq_one_log
import Theorems.Thm_Formalism_FG_FormalGroupCoefficients_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_map_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_map_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_simeqRules
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_mapSimeq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_Top_simeqRules
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_X
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoVariableSwapLemmas_simeq_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_mvExp_add
import Theorems.Thm_Formalism_L2_Th1_D_B4_simeq_sum
import Theorems.Thm_Formalism_L2_Th1_D_FormalExponential_integral_X
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_lgF
import Theorems.Thm_Formalism_L2_Th1_D_Pair_constantCoeff_inVar_eq_zero
import Theorems.Thm_Formalism_L2_Th1_D_Pair_exp_log
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_single_var
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_sum
import Theorems.Thm_Formalism_L2_Th1_D_exponential_specification
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_subst_mvExp__fa9db9cd36a6


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
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus oneLog thetaOne)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB UnrOK IsLawOfLog)
open MvPowerSeries (subst HasSubst constantCoeff)
open SingleLetterLog Pair
namespace Formalism.L2.Th1.D
theorem _root_.solution : OneLetterHalf → SingleLetterThetaFactorization := by
  intro hH K0 K _ _ _ _ _ _ l N0 N1 σ j hU hj F hF be0 hF1 hF2 ζ hζ ph hph U0 Φ hU0 hΦ0 hΦ
  have hl : 2 ≤ l := hU.1.two_le
  have h1 := hH K0 l σ hU F hF be0 hF1 hF2 ζ hζ ph hph
  generalize beMean (d := 2) l σ be0 (fun _ : Unit => (1 : K0)) (fun _ => 1) ζ = be at h1 ⊢
  have h2 := (Formalism.InvariantFactorPaths.G7.Top.mapSimeq K0 K Unit j hj).1 _ _ h1
  have hsL0 : HasSubst (fun _ : ZMod 2 => (lgF K0 l : MvPowerSeries Unit K0)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => cc_lgF hl)
  have hsL : HasSubst (fun _ : ZMod 2 => (lgF K l : MvPowerSeries Unit K)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => cc_lgF hl)
  have e2 : MvPowerSeries.map j (MvPowerSeries.C ((2 : K0)⁻¹) *
      subst (fun _ : ZMod 2 => (lgF K0 l : MvPowerSeries Unit K0)) be) =
      MvPowerSeries.C ((2 : K)⁻¹) *
        subst (fun _ : ZMod 2 => (lgF K l : MvPowerSeries Unit K)) (MvPowerSeries.map j be) := by
    rw [map_mul, MvPowerSeries.map_C, MvPowerSeries.map_subst hsL0, map_inv₀, map_ofNat]
    have e3 : MvPowerSeries.map j (lgF K0 l : MvPowerSeries Unit K0) = lgF K l :=
      Formalism.InvariantFactorPaths.G7.FormalGroupLaws.map_lgF j l
    simp only [e3]
  rw [e2] at h2
  obtain ⟨-, hsymm, htrans, -, -⟩ := Formalism.InvariantFactorPaths.G7.Top.simeqRules K (Fin N0 × Fin N1)
  have hsub := (Formalism.InvariantFactorPaths.G7.Top.simeqRules K Unit).2.2.2.2 (Fin N0 × Fin N1)
  have h3 : ∀ x : Fin N0 × Fin N1, Simeq (at1 x (PowerSeries.map j ph))
      (MvPowerSeries.C ((2 : K)⁻¹) *
        subst (fun _ : ZMod 2 => at1 x (lgF K l)) (MvPowerSeries.map j be)) := by
    intro x
    have hsx : HasSubst (fun _ : Unit => (MvPowerSeries.X x : MvPowerSeries (Fin N0 × Fin N1) K)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
    have h4 := hsub _ _ (fun _ : Unit => (MvPowerSeries.X x : MvPowerSeries (Fin N0 × Fin N1) K))
      (fun _ => by simp) (fun _ => Formalism.InvariantFactorPaths.G7.TwoS.integral_X x) h2
    rw [MvPowerSeries.subst_mul hsx, MvPowerSeries.subst_C,
      MvPowerSeries.subst_comp_subst_apply hsL hsx] at h4
    exact h4
  have h5 := hsymm _ _ (htrans _ _ _ hΦ (B4.simeq_sum Finset.univ _ _ fun x _ => h3 x))
  obtain ⟨h50, h5I⟩ := h5
  set Bt : MvPowerSeries (Fin N0 × Fin N1) K := ∑ x : Fin N0 × Fin N1, MvPowerSeries.C ((2 : K)⁻¹) *
        subst (fun _ : ZMod 2 => at1 x (lgF K l)) (MvPowerSeries.map j be) with hBt
  have hBt0 : constantCoeff Bt = 0 := by
    rw [map_sub, hΦ0, sub_zero] at h50
    exact h50
  refine ⟨mvExp (Bt - Φ) * U0, Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' h5I hU0, ?_⟩
  intro g hg0 hg
  have hsg : HasSubst g := MvPowerSeries.hasSubst_of_constantCoeff_zero hg0
  have hlg : ∀ y, PowerSeries.subst (g y) (lgF K l) = MvPowerSeries.X y := by
    intro y
    rw [← subst_single_var hsg, at_variable_artin_hasse_eq_one_log]
    exact hg y
  have hgE : (fun x => at1 x (expF K l)) = g := by
    funext y
    have h6 := exp_log exponential_specification hl (hg0 y)
    rw [hlg y] at h6
    exact h6
  rw [hgE]
  have e5 : mvExp (-Φ) = mvExp (Bt - Φ) * mvExp (-Bt) := by
    rw [← Formalism.InvariantFactorPaths.G7.mvExp_add h50 (by rw [map_neg, hBt0, neg_zero])]
    congr 1
    ring
  have e6 : subst g (-Bt) = ((-1 : K) / 2) • ∑ x : Fin N0 × Fin N1, subst
      (fun s : ZMod 2 => (if s = 0 then (1 : K) else 1) •
        (MvPowerSeries.X x : MvPowerSeries (Fin N0 × Fin N1) K)) (MvPowerSeries.map j be) := by
    have hsa : ∀ x : Fin N0 × Fin N1, HasSubst (fun _ : ZMod 2 => at1 x (lgF K l)) := fun x =>
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => constantCoeff_inVar_eq_zero x (cc_lgF hl))
    rw [← MvPowerSeries.coe_substAlgHom hsg, map_neg, MvPowerSeries.coe_substAlgHom hsg, hBt,
      subst_sum hsg, MvPowerSeries.smul_eq_C_mul, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [MvPowerSeries.subst_mul hsg, MvPowerSeries.subst_C,
      MvPowerSeries.subst_comp_subst_apply (hsa x) hsg]
    simp only [subst_single_var hsg, hlg, ite_self, one_smul]
    rw [← neg_mul, ← map_neg]
    congr 2
    ring
  unfold thetaOne
  rw [e5, mul_right_comm, MvPowerSeries.subst_mul hsg,
    Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.subst_mvExp' hsg (by rw [map_neg, hBt0, neg_zero]), e6]
end Formalism.L2.Th1.D
