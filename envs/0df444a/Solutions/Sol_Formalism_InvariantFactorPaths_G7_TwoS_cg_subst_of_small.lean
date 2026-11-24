-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.cg_subst_of_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:36.828857+00:00
-- url     : https://prove2.me/submissions/b680f92e-8fa7-49de-b65a-e4000ad6a697

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_pinv_nonneg
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
variable {K : Type} [NormedField K] [IsUltrametricDist K] {ν r0 r1 : ℕ}
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution {ι : Type} {p : ℕ} {L : MvPowerSeries ι K}
    (hL0 : MvPowerSeries.constantCoeff L = 0) (hL : Integral L) {μ μ' : PowerSeries K}
    (h : ∀ n, ‖PowerSeries.coeff n (μ - μ')‖ ≤ (p : ℝ)⁻¹) :
    Cg p (PowerSeries.subst L μ) (PowerSeries.subst L μ') := by
  intro n
  have hs : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero hL0
  rw [← PowerSeries.subst_sub hs, PowerSeries.coeff_subst hs]
  refine norm_finsum_le_of (pinv_nonneg p) fun d => ?_
  rw [smul_eq_mul, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (integral_pow hL d n)).trans (h d)
end Formalism.InvariantFactorPaths.G7.TwoS
