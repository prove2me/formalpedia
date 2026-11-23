-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.pi_factorial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:57:24.049803+00:00
-- url     : https://prove2.me/submissions/ae30150c-7045-4eb3-be44-b893e5c317a6

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_norm_natCast_eq_pow_padicValNat


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
theorem _root_.solution : PiFactorial := by
  intro K _ _ p ϖ hp hnp hϖ i
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlt : ‖(p : K)‖ < 1 := by rw [hnp]; exact inv_lt_one_of_one_lt₀ hp1
  have hpow : ‖ϖ‖ ^ (p ^ 2 - 1) = ‖(p : K)‖ := by rw [← norm_pow, hϖ]
  have hne : p ^ 2 - 1 ≠ 0 := by
    have : 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hp.two_le 2
    omega
  have hle : ‖ϖ‖ ≤ 1 := by
    rw [← pow_le_one_iff_of_nonneg (norm_nonneg ϖ) hne, hpow]; exact hlt.le
  have hfac : (i.factorial : K) ≠ 0 := by
    intro h
    have h2 := Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat (K := K) hp hlt (Nat.factorial_ne_zero i)
    rw [h, norm_zero, hnp] at h2
    exact absurd h2.symm (by positivity)
  rw [norm_div, div_le_one (norm_pos_iff.mpr hfac),
    Formalism.DworkPowerSeriesWeights.norm_natCast_eq_pow_padicValNat hp hlt (Nat.factorial_ne_zero i), ← hpow, ← pow_mul,
    norm_pow]
  refine pow_le_pow_of_le_one (norm_nonneg _) hle ?_
  have : Fact p.Prime := ⟨hp⟩
  have hleg := sub_one_mul_padicValNat_factorial (p := p) i
  have hsq : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    simp only [Nat.add_sub_cancel]
    have : (m + 1) ^ 2 = (m + 1 + 1) * m + 1 := by ring
    omega
  rw [hsq, mul_assoc, hleg]
  exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
end Formalism.InvariantFactorPaths.G7
