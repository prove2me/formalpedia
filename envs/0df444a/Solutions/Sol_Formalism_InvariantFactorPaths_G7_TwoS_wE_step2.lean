-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.wE_step2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:09.523586+00:00
-- url     : https://prove2.me/submissions/71bb8572-8b42-4ec5-ba79-cffe98863832

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_pinv_nonneg
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_norm_pow_sub_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_val_add_two_mod_two
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
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution [NeZero ν] {p : ℕ} (hp : p ≠ 0) {u : ZMod (2 * ν) → K} (hu : ∀ s, ‖u s‖ ≤ 1)
    (hu2 : ∀ s, ‖u (s + 1) - u s ^ p‖ ≤ (p : ℝ)⁻¹) (k : ℕ) (s : ZMod (2 * ν)) :
    ‖wE u k (s + 2) - wE u k s ^ (p ^ 2)‖ ≤ (p : ℝ)⁻¹ := by
  unfold wE
  rw [val_add_two_mod_two]
  split_ifs
  · have e : s + 2 = s + 1 + 1 := by ring
    have e2 : u (s + 2) - u s ^ (p ^ 2) =
        (u (s + 1 + 1) - u (s + 1) ^ p) + (u (s + 1) ^ p - (u s ^ p) ^ p) := by
      rw [e, ← pow_mul, ← sq]; ring
    rw [e2]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hu2 _)
      (norm_pow_sub_pow (hu _) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hu _))
        (hu2 s) p))
  · rw [zero_pow (pow_ne_zero 2 hp), sub_zero, norm_zero]; exact pinv_nonneg p
end Formalism.InvariantFactorPaths.G7.TwoS
