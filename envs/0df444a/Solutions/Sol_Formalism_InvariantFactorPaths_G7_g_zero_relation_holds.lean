-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.g_zero_relation_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:05:35.138371+00:00
-- url     : https://prove2.me/submissions/4d419323-de99-47f1-a121-b6375e5292d0

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_powq_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_lt_powq
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_powq_succ
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_lgF_ne_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_g0F_of
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_coeff_g0F_ne_zero

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
theorem _root_.solution : OddLogRelation := by
  intro K _ p hp _
  have hp0 : p ≠ 0 := by omega
  rw [← PowerSeries.expand_apply p hp0, ← PowerSeries.expand_apply p hp0]
  constructor
  · ext n
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_expand]
    by_cases hc : ∃ j, n = p * (p ^ 2) ^ j
    · obtain ⟨j, rfl⟩ := hc
      rw [coeff_g0F_of K hp, if_pos (Dvd.intro _ rfl), Nat.mul_div_cancel_left _ (by omega),
        coeff_lgF_pow K hp, pow_succ, mul_inv, mul_comm]
    · have h1 : PowerSeries.coeff n (g0F K p) = 0 := by
        by_contra h
        exact hc (coeff_g0F_ne_zero h)
      rw [h1]
      split_ifs with hd
      · obtain ⟨m, rfl⟩ := hd
        rw [Nat.mul_div_cancel_left _ (by omega)]
        have h2 : PowerSeries.coeff m (lgF K p) = 0 := by
          by_contra h
          obtain ⟨j, rfl⟩ := coeff_lgF_ne_zero h
          exact hc ⟨j, rfl⟩
        rw [h2, mul_zero]
      · rw [mul_zero]
  · ext n
    rw [PowerSeries.coeff_expand, map_sub, PowerSeries.coeff_X]
    by_cases hc : ∃ j, n = (p ^ 2) ^ j
    · obtain ⟨j, rfl⟩ := hc
      rw [coeff_lgF_pow K hp]
      cases j with
      | zero =>
        have : ¬ p ∣ 1 := by
          intro h
          have := Nat.le_of_dvd one_pos h
          omega
        simp [this]
      | succ k =>
        have h1 : (p ^ 2) ^ (k + 1) ≠ 1 := by
          have := lt_powq hp (k + 1)
          have h2 : (p ^ 2) ^ (k + 1) = (p ^ 2) ^ 0 → k + 1 = 0 := powq_inj hp
          intro h
          exact absurd (h2 (by simpa using h)) (by omega)
        rw [if_neg h1, sub_zero, powq_succ, if_pos (Dvd.intro _ rfl),
          Nat.mul_div_cancel_left _ (by omega), coeff_g0F_of K hp]
    · have h1 : PowerSeries.coeff n (lgF K p) = 0 := by
        by_contra h
        exact hc (coeff_lgF_ne_zero h)
      have h2 : n ≠ 1 := fun h => hc ⟨0, by simpa using h⟩
      rw [h1, if_neg h2, sub_zero]
      split_ifs with hd
      · obtain ⟨m, rfl⟩ := hd
        rw [Nat.mul_div_cancel_left _ (by omega)]
        by_contra h
        obtain ⟨j, rfl⟩ := coeff_g0F_ne_zero h
        exact hc ⟨j + 1, (powq_succ p j).symm⟩
      · rfl
end Formalism.InvariantFactorPaths.G7
