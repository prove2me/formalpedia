-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.altR_add_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:45:49.132709+00:00
-- url     : https://prove2.me/submissions/b23da1a5-4a0b-454b-9003-c5026afb3afe

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_CyclicPowerClassOfExpEquiv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartB
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BallRing
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_LogarithmEquivalence
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_coeff_altR_pow
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_coeff_altR_of_not
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
namespace Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
theorem _root_.solution (R : Type) [CommRing R] {p : ℕ} (hp : 2 ≤ p) (hq : p ^ 2 ≠ 0) :
    altR R p + PowerSeries.expand (p ^ 2) hq (altR R p) = PowerSeries.X := by
  ext n
  rw [map_add, PowerSeries.coeff_expand, PowerSeries.coeff_X]
  have hq1 : 1 < p ^ 2 := by nlinarith
  by_cases h : ∃ l, n = (p ^ 2) ^ l
  · obtain ⟨l, rfl⟩ := h
    rcases l with _ | l
    · rw [coeff_altR_pow R hp, pow_zero, pow_zero, if_pos rfl,
        if_neg (fun hd => absurd (Nat.le_of_dvd one_pos hd) (by omega)), add_zero]
    · have h1 : (p ^ 2) ^ (l + 1) ≠ 1 := fun h' =>
        absurd (powq_inj hp (h'.trans (pow_zero _).symm)) (by omega)
      rw [coeff_altR_pow R hp, if_pos (Dvd.intro_left _ (pow_succ _ _).symm), if_neg h1, pow_succ (p ^ 2),
        Nat.mul_div_cancel _ (by omega), coeff_altR_pow R hp]
      ring
  · have h' : ∀ l, n ≠ (p ^ 2) ^ l := fun l hl => h ⟨l, hl⟩
    have h1 : n ≠ 1 := by simpa using h' 0
    rw [coeff_altR_of_not h', if_neg h1, zero_add]
    split_ifs with hd
    · refine coeff_altR_of_not fun l hl => h' (l + 1) ?_
      rw [pow_succ, ← hl, Nat.div_mul_cancel hd]
    · rfl
end Formalism.InvariantFactorPaths.G7.LogarithmEquivalence
