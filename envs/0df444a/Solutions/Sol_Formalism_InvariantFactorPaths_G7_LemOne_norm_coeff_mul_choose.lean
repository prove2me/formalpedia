-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.norm_coeff_mul_choose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:53:27.324208+00:00
-- url     : https://prove2.me/submissions/6901dbad-05c7-4b88-8f41-7d98d4ddd8fc

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_integral_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_degree_pair
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_coeff_pow_top
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_norm_sub_le_max
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_single_variable_series


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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemOne
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.LemOne
theorem _root_.solution {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFi : Integral F)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1)
    {h : PowerSeries K} (hcob : Integral (cob F h)) {n : ℕ}
    (hlow : ∀ d < n, ‖PowerSeries.coeff d h‖ ≤ 1) {i : ℕ} (hi0 : 0 < i) (hin : i < n) :
    ‖PowerSeries.coeff n h * (n.choose i : K)‖ ≤ 1 := by
  classical
  obtain ⟨e, he⟩ : ∃ e : Fin 2 →₀ ℕ, e = Finsupp.single 0 i + Finsupp.single 1 (n - i) := ⟨_, rfl⟩
  have hdeg : e.degree = n := by rw [he, degree_pair]; omega
  have hs : PowerSeries.HasSubst F := PowerSeries.HasSubst.of_constantCoeff_zero hF0
  have e0 : e 0 = i := by simp [he]
  have e1 : e 1 = n - i := by simp [he]
  have h0 : MvPowerSeries.coeff e (at1 0 h) = 0 := by
    rw [coeff_single_variable_series, if_neg]
    intro hh
    have := congrArg (fun u => u 1) hh
    simp [e1] at this
    omega
  have h1 : MvPowerSeries.coeff e (at1 1 h) = 0 := by
    rw [coeff_single_variable_series, if_neg]
    intro hh
    have := congrArg (fun u => u 0) hh
    simp [e0] at this
    omega
  have key : MvPowerSeries.coeff e (PowerSeries.subst F h) =
      ∑ d ∈ range (n + 1), PowerSeries.coeff d h * MvPowerSeries.coeff e (F ^ d) := by
    rw [PowerSeries.coeff_subst hs, finsum_eq_sum_of_support_subset (s := range (n + 1))]
    · simp only [smul_eq_mul]
    · intro d hd
      rw [Function.mem_support] at hd
      rw [Finset.coe_range, Set.mem_Iio]
      by_contra hlt
      apply hd
      rw [MvPowerSeries.coeff_of_lt_order, smul_zero]
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero d hF0)
      rw [hdeg]
      exact_mod_cast (by omega : n < d)
  have htop : MvPowerSeries.coeff e (F ^ n) = (n.choose i : K) := by
    rw [he]; exact coeff_pow_top hF0 hF1 n i hin.le
  have hc := hcob e
  unfold cob at hc
  rw [map_sub, map_sub, h0, h1, sub_zero, sub_zero, key, sum_range_succ, htop] at hc
  have hsum : ‖∑ d ∈ range n, PowerSeries.coeff d h * MvPowerSeries.coeff e (F ^ d)‖ ≤ 1 := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun d hd => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hlow d (mem_range.1 hd)) (norm_nonneg _) (integral_pow hFi d e)
  have hsplit : PowerSeries.coeff n h * (n.choose i : K) =
      (∑ d ∈ range n, PowerSeries.coeff d h * MvPowerSeries.coeff e (F ^ d) +
        PowerSeries.coeff n h * (n.choose i : K)) -
      ∑ d ∈ range n, PowerSeries.coeff d h * MvPowerSeries.coeff e (F ^ d) := by ring
  rw [hsplit]
  exact (norm_sub_le_max _ _).trans (max_le hc hsum)
end Formalism.InvariantFactorPaths.G7.LemOne
