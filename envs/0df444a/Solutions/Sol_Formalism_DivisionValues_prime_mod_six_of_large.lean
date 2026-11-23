-- Prove2me | solution 1 for Formalism.DivisionValues.prime_mod_six_of_large
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:25:04.031967+00:00
-- url     : https://prove2.me/submissions/6e63ff89-0cf7-4881-b3c3-ab9468a1366a

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_UntwistedChoice
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_PlaceSumSquares
import Theorems.Thm_Formalism_DivisionValues_W5_prime_sum_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
namespace Formalism.DivisionValues
theorem _root_.solution : PrimeSumSq := by
  have h1 : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) →
      ∑ p ∈ s, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 999 / 1000 := by
    intro s hs
    have h := W5.prime_sum_le s hs
    have e : ∑ p ∈ s, 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2 =
        2 * ∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => by ring)
    rw [e]
    linarith
  have h2 : ∀ u : Finset Nat.Primes,
      ∑ p ∈ u, 2 * Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 ≤ 999 / 1000 := by
    intro u
    have h := h1 (u.map ⟨Subtype.val, Subtype.val_injective⟩) (by
      intro p hp
      obtain ⟨q, -, rfl⟩ := Finset.mem_map.1 hp
      exact q.2)
    have e := Finset.sum_map u ⟨Subtype.val, Subtype.val_injective⟩
      (fun p : ℕ => 2 * Real.log (p : ℝ) / (p : ℝ) ^ 2)
    exact le_of_eq_of_le e.symm h
  have h0 : 0 ≤ fun p : Nat.Primes => 2 * Real.log ((p : ℕ) : ℝ) / ((p : ℕ) : ℝ) ^ 2 := fun p =>
    div_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg _)) (by positivity)
  exact ⟨h1, summable_of_sum_le h0 h2,
    lt_of_le_of_lt (Real.tsum_le_of_sum_le h0 h2) (by norm_num)⟩
end Formalism.DivisionValues
