-- Prove2me | solution 1 for Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding.orderOf_five_units_two_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:37:22.660822+00:00
-- url     : https://prove2.me/submissions/a3d033ac-6fd6-43e6-8a96-2ecaa57c74c4

import Mathlib
import Definitions.Def_Formalism_TameInertiaTowers_StatementGroup
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_MemDecompositionSubgroupIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Subgroup
namespace Formalism.TwoAdicCyclotomicDecomposition
namespace ModelEmbedding
end ModelEmbedding
open ModelEmbedding
namespace ModelEmbedding
private lemma exists_five_pow_two_pow_eq_one_add (m : ℕ) : ∃ t : ℕ, 5 ^ (2 ^ m) = 1 + 2 ^ (m + 2) * (2 * t + 1) := by
  induction m with
  | zero => exact ⟨0, by norm_num⟩
  | succ m ih =>
    obtain ⟨t, ht⟩ := ih
    refine ⟨t + 2 ^ m * (2 * t + 1) ^ 2, ?_⟩
    rw [pow_succ 2 m, pow_mul, ht]
    ring
end ModelEmbedding
open ModelEmbedding
namespace ModelEmbedding
end ModelEmbedding
open ModelEmbedding
end Formalism.TwoAdicCyclotomicDecomposition
end

set_option autoImplicit false
open Subgroup
open Formalism Formalism.TwoAdicCyclotomicDecomposition
open ModelEmbedding
open Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
namespace Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
theorem _root_.solution (k : ℕ) : orderOf (u5 (k + 2)) = 2 ^ k := by
  have hpow : ∀ N j : ℕ, u5 N ^ j = 1 ↔ 5 ^ j ≡ 1 [MOD 2 ^ N] := by
    intro N j
    rw [← ZMod.natCast_eq_natCast_iff, Units.ext_iff]
    simp [u5]
  cases k with
  | zero =>
    rw [pow_zero, orderOf_eq_one_iff, ← pow_one (u5 (0 + 2)), hpow]
    decide
  | succ m =>
    apply orderOf_eq_prime_pow
    · rw [hpow]
      obtain ⟨t, ht⟩ := exists_five_pow_two_pow_eq_one_add m
      rw [ht]
      intro h
      have h2 := (Nat.modEq_iff_dvd' (by omega)).1 h.symm
      rw [Nat.add_sub_cancel_left, show m + 1 + 2 = (m + 2) + 1 by ring, pow_succ] at h2
      have h3 := Nat.dvd_of_mul_dvd_mul_left (by positivity) h2
      omega
    · rw [hpow]
      obtain ⟨t, ht⟩ := exists_five_pow_two_pow_eq_one_add (m + 1)
      rw [ht]
      exact ((Nat.modEq_iff_dvd' (by omega)).2
        (by rw [Nat.add_sub_cancel_left]; exact dvd_mul_right _ _)).symm
end Formalism.TwoAdicCyclotomicDecomposition.ModelEmbedding
