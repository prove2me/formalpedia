-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.wt_AA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:24.596468+00:00
-- url     : https://prove2.me/submissions/7057490b-7f35-438a-a2a4-8aa4b1953978

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_LogarithmWeightComparison
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_leadT_eq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_degree_fin_two_eq_add_of_ne
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_dot_const
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_low_subst_of_low
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_substitution_weight_bound
import Theorems.Thm_Formalism_FG_SolveVAux_low_add
import Theorems.Thm_Formalism_FG_SolveVAux_low_mono
import Theorems.Thm_Formalism_FG_SolveVAux_low_mul
import Theorems.Thm_Formalism_FG_SolveVAux_low_neg
import Theorems.Thm_Formalism_FG_SolveVAux_low_one_iff
import Theorems.Thm_Formalism_FG_SolveVAux_low_pow
import Theorems.Thm_Formalism_FG_SolveVAux_low_sub
import Theorems.Thm_Formalism_FG_SolveVAux_low_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_AA_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_AA_of
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_finset_fin_two_eq_cases


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp low_subst_of_low WtGe MonoWtGe dot dot_const substitution_weight_bound)
open Formalism.FG.SolveVAux (Low low_zero low_mono low_add low_sub low_neg low_mul low_pow low_one_iff)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hT : ValTable) {K : Type} [NormedField K] {p : ℕ} (hp : p.Prime)
    (hn : ‖(p : K)‖ = (p : ℝ)⁻¹) {x y : Fin 2} (hxy : x ≠ y) (d : Fin 2 →₀ ℕ) :
    ‖MvPowerSeries.coeff d (AA K p x y - leadT K p x y)‖ ≤
      ((p : ℝ)⁻¹) ^ (1 / ((p : ℝ) - 1) - (d.degree : ℝ) * (1 / ((p : ℝ) ^ 2 - 1))) := by
  classical
  have hp2 := hp.two_le
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by positivity
  have hle : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  rw [map_sub, leadT_eq, MvPowerSeries.coeff_monomial]
  by_cases hd : d = Finsupp.single x 1 + Finsupp.single y p
  · have hx : d x = (p ^ 2) ^ 0 := by rw [hd]; simp [hxy.symm]
    have hy : d y = p * (p ^ 2) ^ 0 := by rw [hd]; simp [hxy]
    rw [if_pos hd, coeff_AA_of K hp2 le_rfl hx hy]
    simp only [add_zero, zero_add, pow_one, sub_self, norm_zero]
    positivity
  · rw [if_neg hd, sub_zero]
    by_cases h : MvPowerSeries.coeff d (AA K p x y) = 0
    · rw [h, norm_zero]; positivity
    · obtain ⟨i, j, hij, hx, hy⟩ := coeff_AA_ne_zero h
      have hj : 1 ≤ j := by
        by_contra hj
        obtain rfl : j = 0 := by omega
        obtain rfl : i = 0 := by omega
        apply hd
        ext z
        rcases finset_fin_two_eq_cases x y hxy z with rfl | rfl
        · simp [hx, hxy.symm]
        · simp [hy, hxy]
      rw [coeff_AA_of K hp2 hij hx hy, norm_inv, norm_pow, hn, ← Real.rpow_natCast,
        ← Real.rpow_neg hpos.le]
      refine Real.rpow_le_rpow_of_exponent_ge hpos hle ?_
      have h1 := (hT p i j hp2 hij).2 hj
      have e := div_eq_mul_one_div (((p : ℝ) ^ 2) ^ i + p * ((p : ℝ) ^ 2) ^ j) ((p : ℝ) ^ 2 - 1)
      rw [degree_fin_two_eq_add_of_ne hxy, hx, hy]
      push_cast
      linarith
end Formalism.InvariantFactorPaths.G7
