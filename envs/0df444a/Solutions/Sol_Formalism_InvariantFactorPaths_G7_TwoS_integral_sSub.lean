-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.integral_sSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:09:52.195955+00:00
-- url     : https://prove2.me/submissions/9b646f3e-ed35-4ef6-a38d-707f4ba29be5

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_of_cg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_posW
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_norm_wE
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_mu_lin
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_zLin_false
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_zLin_true
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
    {om oms : Fin ν → ZMod (2 * ν) → K} (hO : OmOK p ν om oms) {μ : PowerSeries K}
    (hμ : ∀ n, ‖PowerSeries.coeff n (μ - altF K p)‖ ≤ (p : ℝ)⁻¹) (x : Bool × EV ν r0 r1) :
    Integral (sSub om oms μ x) := by
  obtain ⟨hO1, hO2, -⟩ := hO
  obtain ⟨b, e⟩ := x
  unfold sSub
  cases b
  · rw [zLin_false]
    exact integral_of_cg (cg_mu_lin hp hn (fun s => (hO1 e.1 s).2) (fun s => (hO2 e.1 s).2) 0 e.2 hμ)
      (integral_posW p (norm_wE (fun s => (hO1 e.1 s).2) 0) e.2)
  · rw [zLin_true]
    exact integral_of_cg (cg_mu_lin hp hn (fun s => (hO1 e.1 s).1) (fun s => (hO2 e.1 s).1) 1 e.2 hμ)
      (integral_posW p (norm_wE (fun s => (hO1 e.1 s).1) 1) e.2)
end Formalism.InvariantFactorPaths.G7.TwoS
