-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.cg_two_sums
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:26:17.739006+00:00
-- url     : https://prove2.me/submissions/2a9a021f-7521-479a-8976-24f3ab7db598

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_refl
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_sub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_posW
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_norm_wE
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_TwoS_norm_wE__43050fc77372
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_TwoS_integral_posW__09bbc0735fe1
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_mu_lin
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_mu_lin_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_zLin_false
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_zLin_true
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_constantCoeff_sSub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_sSub
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_subst_hh_eq_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_hhS_eq
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow


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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low norm_finsum_le_of)
open Formalism.FG.SolveVAux (Low low_pow low_one_iff)
open Formalism.FG.IntegralSubstitution (integral_mul integral_pow integral_one integralSubstV)
open Formalism.InvariantFactorPaths.G7.TwoS
variable {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ} [NeZero ν]
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {om oms : Fin ν → ZMod (2 * ν) → K} (hO : OmOK p ν om oms) {c c' : K} (hc : ‖c‖ ≤ 1)
    (hc' : ‖c'‖ ≤ 1) {μ : PowerSeries K} (hμ0 : PowerSeries.constantCoeff μ = 0)
    (hμ : ∀ n, ‖PowerSeries.coeff n (μ - altF K p)‖ ≤ (p : ℝ)⁻¹) :
    Cg p (MvPowerSeries.subst (sSub om oms μ) (hh1 (E := EV ν r0 r1) p c c'))
      (hhS p (uS c c')) := by
  have hs : MvPowerSeries.HasSubst (sSub (r0 := r0) (r1 := r1) om oms μ) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_sSub om oms hμ0)
  have hI := integral_sSub (r0 := r0) (r1 := r1) hp hn hO hμ
  obtain ⟨hO1, hO2, hO3⟩ := hO
  rw [subst_hh_eq_sum p c c' hs, hhS_eq hO3]
  refine cg_sum _ _ _ fun e _ => ?_
  have aF := cg_mu_lin hp hn (fun s => (hO1 e.1 s).2) (fun s => (hO2 e.1 s).2) 0 e.2 hμ
  have aT := cg_mu_lin hp hn (fun s => (hO1 e.1 s).1) (fun s => (hO2 e.1 s).1) 1 e.2 hμ
  have bF := cg_mu_lin_pow hp hn (fun s => (hO1 e.1 s).2) (fun s => (hO2 e.1 s).2) 0 e.2 hμ
  have bT := cg_mu_lin_pow hp hn (fun s => (hO1 e.1 s).1) (fun s => (hO2 e.1 s).1) 1 e.2 hμ
  rw [← zLin_false om oms e] at aF bF
  rw [← zLin_true om oms e] at aT bT
  have iF := hI (false, e)
  have iT := hI (true, e)
  refine cg_sub (cg_mul (integral_mul (integral_C hc) iF)
      (integral_posW' p (norm_wE' (fun s => (hO1 e.1 s).1) 1) e.2)
      (cg_mul (integral_C hc) (integral_posW p (norm_wE (fun s => (hO1 e.1 s).2) 0) e.2)
        (cg_refl p _) aF) bT)
    (cg_mul (integral_mul (integral_C hc') (integral_pow iF p))
      (integral_posW p (norm_wE (fun s => (hO1 e.1 s).1) 1) e.2)
      (cg_mul (integral_C hc') (integral_posW' p (norm_wE' (fun s => (hO1 e.1 s).2) 0) e.2)
        (cg_refl p _) bF) aT)
end Formalism.InvariantFactorPaths.G7.TwoS
