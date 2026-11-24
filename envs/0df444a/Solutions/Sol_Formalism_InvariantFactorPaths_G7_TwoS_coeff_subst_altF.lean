-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.TwoS.coeff_subst_altF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:41:43.037926+00:00
-- url     : https://prove2.me/submissions/49707a12-2078-4d86-96e4-08cffa5c3525

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TheoremSFromKOneOf
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_coeff_altF_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_TwoS_coeff_altF_ne_zero
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_finsum_le_of
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integralSubstV
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_mul
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_one
import Theorems.Thm_Formalism_FG_IntegralSubstitution_integral_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_lt_powq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_powq_inj


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
variable {K : Type} [Field K]
namespace Formalism.InvariantFactorPaths.G7.TwoS
theorem _root_.solution {ι : Type} {p : ℕ} (hp : 2 ≤ p) {L : MvPowerSeries ι K}
    (hL : MvPowerSeries.constantCoeff L = 0) (n : ι →₀ ℕ) :
    MvPowerSeries.coeff n (PowerSeries.subst L (altF K p)) =
      ∑ l ∈ range (n.degree + 1), (-1) ^ l * MvPowerSeries.coeff n (L ^ ((p ^ 2) ^ l)) := by
  classical
  have hs : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero hL
  rw [PowerSeries.coeff_subst hs,
    finsum_eq_sum_of_support_subset (s := (range (n.degree + 1)).image fun l => (p ^ 2) ^ l)]
  · rw [Finset.sum_image fun a _ b _ h => powq_inj hp h]
    exact Finset.sum_congr rfl fun l _ => by rw [coeff_altF_pow hp, smul_eq_mul]
  · intro d hd
    simp only [Function.mem_support] at hd
    have h1 : PowerSeries.coeff d (altF K p) ≠ 0 := fun h => hd (by rw [h, zero_smul])
    have h2 : MvPowerSeries.coeff n (L ^ d) ≠ 0 := fun h => hd (by rw [h, smul_zero])
    obtain ⟨l, rfl⟩ := coeff_altF_ne_zero h1
    have h3 : (p ^ 2) ^ l ≤ n.degree := by
      by_contra hlt
      exact h2 (low_pow ((low_one_iff _).2 hL) _ n (by omega))
    simp only [Finset.coe_image, Set.mem_image, Finset.coe_range, Set.mem_Iio]
    exact ⟨l, by have := lt_powq hp l; omega, rfl⟩
end Formalism.InvariantFactorPaths.G7.TwoS
