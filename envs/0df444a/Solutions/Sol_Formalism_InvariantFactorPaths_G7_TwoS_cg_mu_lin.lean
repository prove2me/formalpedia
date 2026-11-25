-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.cg_mu_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:59:59.303102+00:00
-- url     : https://prove2.me/submissions/4981ee02-dd55-4ccd-a61a-a7be2637337c

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_trans
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_constantCoeff_linW
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_linW
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_altF_lin
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_subst_of_small
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_norm_wE
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_wE_step2
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
variable {ν : ℕ}
variable {K : Type}
variable [NormedField K] [IsUltrametricDist K]
variable {r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution [NeZero ν] {p : ℕ} (hp : p.Prime) (hn : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {u : ZMod (2 * ν) → K} (hu : ∀ s, ‖u s‖ ≤ 1)
    (hu2 : ∀ s, ‖u (s + 1) - u s ^ p‖ ≤ (p : ℝ)⁻¹) (k : ℕ) (ab : Fin r0 × Fin r1)
    {μ : PowerSeries K} (hμ : ∀ n, ‖PowerSeries.coeff n (μ - altF K p)‖ ≤ (p : ℝ)⁻¹) :
    Cg p (PowerSeries.subst (linW (wE u k) ab) μ) (posW p (wE u k) ab) :=
  cg_trans (cg_subst_of_small (constantCoeff_linW _ _) (integral_linW (norm_wE hu k) ab) hμ)
    (cg_altF_lin hp hn (norm_wE hu k) (wE_step2 hp.ne_zero hu hu2 k) ab)
end Formalism.InvariantFactorPaths.G7.TwoS
