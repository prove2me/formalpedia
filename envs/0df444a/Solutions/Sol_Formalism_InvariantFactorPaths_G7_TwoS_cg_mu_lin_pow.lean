-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.cg_mu_lin_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:17:38.025591+00:00
-- url     : https://prove2.me/submissions/f3e23e37-5252-427d-bfe0-da9674184e6a

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_refl
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_trans
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_of_cg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_C
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_frob_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_sPos
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_integral_posW
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_norm_wE
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_TwoS_wE__step_f30d06da0158
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_cg_mu_lin
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
    Cg p (PowerSeries.subst (linW (wE u k) ab) μ ^ p) (posW' p (wE' u k) ab) := by
  have hA := cg_mu_lin hp hn hu hu2 k ab hμ
  have hI := integral_posW (r0 := r0) (r1 := r1) p (norm_wE hu k) ab
  refine cg_trans (cg_pow (integral_of_cg hA hI) hI hA p) ?_
  refine cg_trans (cg_frob_sum hp hn Finset.univ _ fun s _ =>
    integral_mul (integral_C (norm_wE hu k s)) (integral_sPos p s ab)) ?_
  refine cg_sum _ _ _ fun s _ => ?_
  rw [mul_pow, ← map_pow]
  refine cg_mul (integral_C ?_) (integral_pow (integral_sPos p s ab) p)
    (cg_C (wE'_step hp.ne_zero hu2 k s)) (cg_refl _ _)
  rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_wE hu k s)
end Formalism.InvariantFactorPaths.G7.TwoS
