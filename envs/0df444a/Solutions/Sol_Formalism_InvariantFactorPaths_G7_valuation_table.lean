-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.valuation_table
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:43.085086+00:00
-- url     : https://prove2.me/submissions/1c10397d-36c9-46f4-8c49-7112332039ec

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_OddLogRelation
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_NormNatCastEqPowPadicValNat
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA

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
theorem _root_.solution : ValTable := by
  intro p i j hp hij
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hq1 : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hq0 : (p : ℝ) ^ 2 - 1 ≠ 0 := hq1.ne'
  have hp0 : (p : ℝ) - 1 ≠ 0 := hp1.ne'
  have hLHS : 1 / ((p : ℝ) - 1) + p - 2 = (1 + p * (p : ℝ) ^ 2) / ((p : ℝ) ^ 2 - 1) - 2 := by
    field_simp
    ring
  constructor
  · intro hj
    subst hj
    have hi : i = 0 := by omega
    subst hi
    simp only [pow_zero, mul_one, Nat.cast_zero, zero_add]
    field_simp
    ring
  · intro hj
    rw [hLHS]
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hB : ∀ m : ℕ, 1 + (m : ℝ) * ((p : ℝ) ^ 2 - 1) ≤ ((p : ℝ) ^ 2) ^ m := by
      intro m
      have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ (p : ℝ) ^ 2 - 1 by nlinarith) m
      have e : (1 : ℝ) + ((p : ℝ) ^ 2 - 1) = (p : ℝ) ^ 2 := by ring
      rw [e] at h
      exact h
    have h1 := hB i
    have h2 := hB k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) * ((p : ℝ) ^ 2 - 1) := mul_nonneg (Nat.cast_nonneg k) hq1.le
    have hpk : (0 : ℝ) ≤ ((p : ℝ) ^ 2) ^ k - 1 := by linarith
    have hpq : (1 : ℝ) ≤ p * (p : ℝ) ^ 2 := by nlinarith
    have hsplit : (((p : ℝ) ^ 2) ^ i + p * ((p : ℝ) ^ 2) ^ (k + 1)) / ((p : ℝ) ^ 2 - 1) -
        (1 + p * (p : ℝ) ^ 2) / ((p : ℝ) ^ 2 - 1) =
        (((p : ℝ) ^ 2) ^ i + p * ((p : ℝ) ^ 2) ^ (k + 1) - 1 - p * (p : ℝ) ^ 2) /
          ((p : ℝ) ^ 2 - 1) := by
      ring
    have hmain : (i : ℝ) + k ≤
        (((p : ℝ) ^ 2) ^ i + p * ((p : ℝ) ^ 2) ^ (k + 1) - 1 - p * (p : ℝ) ^ 2) /
          ((p : ℝ) ^ 2 - 1) := by
      rw [le_div_iff₀ hq1, pow_succ ((p : ℝ) ^ 2) k]
      nlinarith [mul_nonneg (sub_nonneg.mpr hpq) hpk]
    push_cast
    linarith
end Formalism.InvariantFactorPaths.G7
