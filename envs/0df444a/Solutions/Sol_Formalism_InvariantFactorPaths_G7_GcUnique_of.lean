-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.GcUnique_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:27:23.486132+00:00
-- url     : https://prove2.me/submissions/04ca0538-67cf-4379-9593-2987cd40d7ac

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_ThmSUniform
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_OmegaOfTraceDuality
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_eq_zero_of_div
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_map_Gser
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemTwo_eq_zero_of_div
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_g0F_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_g0F_of
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_product_single_variables


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
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (hD : DworkMv) (hFr : FrobExprG) : GcUnique := by
  intro K _ _ _ p σ hU c d hc hd hsim
  obtain ⟨hp, -, hnp, -, hσ⟩ := hU
  have hp2 : 2 ≤ p := hp.two_le
  have hpK : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hlin : Gser p c (σ c) - Gser p d (σ d) = Gser p (c - d) (σ (c - d)) := by
    simp only [Gser, map_sub]
    ring
  have hee : σ (σ (c - d)) = c - d := by rw [map_sub, map_sub, hc, hd]
  obtain ⟨h0, hI⟩ := hsim
  rw [hlin] at h0 hI
  have hDw := (hD K (Fin 2) p σ hp hnp hσ _ h0).1 hI
  rw [CoboundarySeries.map_Gser, hee, hFr K p (c - d) (σ (c - d)) hp2 hpK] at hDw
  have hl1 : PowerSeries.coeff 1 (lgF K p) = 1 := by
    have h := coeff_lgF_pow K hp2 0
    simpa using h
  have hg1 : PowerSeries.coeff 1 (g0F K p) = 0 := by
    by_contra h
    obtain ⟨j, hj⟩ := coeff_g0F_ne_zero h
    have h1 : p ∣ 1 := ⟨_, hj⟩
    have := Nat.le_of_dvd one_pos h1
    omega
  have hz : c - d = 0 := by
    apply CoboundarySeries.eq_zero_of_div hp2 hnp
    intro i
    have h := hDw (Finsupp.single 0 1 + Finsupp.single 1 (p * (p ^ 2) ^ i))
    have hn0 : (Finsupp.single 0 1 + Finsupp.single 1 (p * (p ^ 2) ^ i) : Fin 2 →₀ ℕ) 0 = 1 := by
      simp
    have hn1 : (Finsupp.single 0 1 + Finsupp.single 1 (p * (p ^ 2) ^ i) : Fin 2 →₀ ℕ) 1 =
        p * (p ^ 2) ^ i := by
      simp
    rw [MvPowerSeries.coeff_C_mul, map_sub, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_C_mul,
      coeff_product_single_variables (by decide) (by decide), coeff_product_single_variables (by decide) (by decide),
      hn0, hn1, hl1, hg1, coeff_g0F_of K hp2 i, zero_mul, mul_zero, zero_sub, one_mul, norm_mul,
      norm_neg, hnp] at h
    have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := by
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
      positivity
    exact le_of_mul_le_mul_left (by simpa using h) hpos
  exact sub_eq_zero.mp hz
end Formalism.InvariantFactorPaths.G7
