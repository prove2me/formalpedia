-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.good_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:19:02.809838+00:00
-- url     : https://prove2.me/submissions/0f83ff83-4ceb-49ac-b733-5de0c5924950

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_norm_p_lt_one
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_norm_coeff_of_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_correct
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_g_zero_low_coeff_norm
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_lg_low
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_cob_rem_integral
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_g0F_of
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_pow


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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFi : Integral F)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1)
    (hFl : cob F (lgF K p) = 0) (hde : Integral (cob F (g0F K p)))
    {f : PowerSeries K} (hcob : Integral (cob F f)) (j : ℕ) (a b : K) (hG : Good p f j a b) :
    ∃ a' b' : K, Good p f (j + 1) a' b' ∧ ‖a' - a‖ ≤ ((p : ℝ)⁻¹) ^ j ∧
      ‖b' - b‖ ≤ ((p : ℝ)⁻¹) ^ j := by
  obtain ⟨ha, hlow⟩ := hG
  have hple : ‖(p : K) ^ j‖ ≤ 1 := by
    rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (norm_p_lt_one hp hnp).le

  obtain ⟨μ, hμdef⟩ : ∃ μ : K, μ = (p : K) * PowerSeries.coeff (p ^ (2 * j + 1)) (rem p f a b) :=
    ⟨_, rfl⟩
  have hμ0 := norm_coeff_of_pow hp hnp hF0 hFi hF1 (cob_rem_integral hF0 hFl hde hcob ha b)
    (2 * j) hlow
  rw [← hμdef] at hμ0
  have ha' : ‖a + μ * (p : K) ^ j‖ ≤ 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha ?_)
    rw [norm_mul]
    exact mul_le_one₀ hμ0 (norm_nonneg _) hple
  have e1 : rem p f (a + μ * (p : K) ^ j) b = rem p f a b -
      PowerSeries.C ((p : K) * PowerSeries.coeff (p ^ (2 * j + 1)) (rem p f a b) * (p : K) ^ j) *
        g0F K p := by
    rw [← hμdef]
    unfold rem
    rw [map_add]
    ring
  have htop1 : PowerSeries.coeff (p ^ (2 * j + 1)) (g0F K p) = ((p : K) ^ (j + 1))⁻¹ := by
    have e : p ^ (2 * j + 1) = p * (p ^ 2) ^ j := by ring
    rw [e]
    exact coeff_g0F_of K hp.two_le j
  obtain ⟨-, hlow1⟩ := correct hp hnp hF0 hFi hF1 (cob_rem_integral hF0 hFl hde hcob ha b) (2 * j) j
    hlow (g_zero_low_coeff_norm hp hnp j) htop1 e1 (cob_rem_integral hF0 hFl hde hcob ha' b)

  obtain ⟨ν, hνdef⟩ : ∃ ν : K, ν = (p : K) *
      PowerSeries.coeff (p ^ (2 * j + 1 + 1)) (rem p f (a + μ * (p : K) ^ j) b) := ⟨_, rfl⟩
  have e2 : rem p f (a + μ * (p : K) ^ j) (b + ν * (p : K) ^ j) =
      rem p f (a + μ * (p : K) ^ j) b -
      PowerSeries.C ((p : K) * PowerSeries.coeff (p ^ (2 * j + 1 + 1))
        (rem p f (a + μ * (p : K) ^ j) b) * (p : K) ^ j) * lgF K p := by
    rw [← hνdef]
    unfold rem
    rw [map_add (PowerSeries.C) b]
    ring
  have htop2 : PowerSeries.coeff (p ^ (2 * j + 1 + 1)) (lgF K p) = ((p : K) ^ (j + 1))⁻¹ := by
    have e : p ^ (2 * j + 1 + 1) = (p ^ 2) ^ (j + 1) := by ring
    rw [e]
    exact coeff_lgF_pow K hp.two_le (j + 1)
  obtain ⟨hν0, hlow2⟩ := correct hp hnp hF0 hFi hF1 (cob_rem_integral hF0 hFl hde hcob ha' b)
    (2 * j + 1) j hlow1 (lg_low hp hnp j) htop2 e2 (cob_rem_integral hF0 hFl hde hcob ha' _)
  rw [← hνdef] at hν0
  refine ⟨a + μ * (p : K) ^ j, b + ν * (p : K) ^ j, ⟨ha', hlow2⟩, ?_, ?_⟩
  · rw [add_sub_cancel_left, norm_mul, norm_pow, hnp]
    exact mul_le_of_le_one_left (by positivity) hμ0
  · rw [add_sub_cancel_left, norm_mul, norm_pow, hnp]
    exact mul_le_of_le_one_left (by positivity) hν0
end Formalism.InvariantFactorPaths.G7.LemOne
