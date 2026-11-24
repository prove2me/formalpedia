-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.choose_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:33:25.762721+00:00
-- url     : https://prove2.me/submissions/64ee37f4-5ff7-4ef3-b361-0b35b9592ffb

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Theorems.Thm_Formalism_MainNotions_PlaneGram_one_add_X_pow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) {σ : Type}
variable {v}
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (ρ P m : ℕ) : ∃ z : ℕ → ℕ, ∀ β : ℕ,
    (ρ + P * β).choose m = ∑ i ∈ range (m + 1), z i * β.choose i := by
  obtain ⟨Q, hQ⟩ := one_add_X_pow_eq P
  refine ⟨fun i => (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i).coeff m,
    fun β => ?_⟩
  have hz : ∀ i, m < i →
      (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i).coeff m = 0 := by
    intro i hi
    rw [show ((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i =
        ((1 + Polynomial.X) ^ ρ * Q ^ i) * Polynomial.X ^ i by ring,
      Polynomial.coeff_mul_X_pow', if_neg (by omega)]
  have hL : ∀ i, (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) *
      ((Polynomial.X * Q) ^ i * 1 ^ (β - i) * ((β.choose i : ℕ) : Polynomial ℕ))).coeff m =
      (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i).coeff m * β.choose i := by
    intro i
    rw [one_pow, mul_one, ← mul_assoc, Polynomial.coeff_mul_natCast, Nat.cast_id]
  have h1 : (ρ + P * β).choose m = ((1 + Polynomial.X : Polynomial ℕ) ^ (ρ + P * β)).coeff m := by
    rw [Polynomial.coeff_one_add_X_pow, Nat.cast_id]
  rw [h1, pow_add, pow_mul, hQ, add_comm (1 : Polynomial ℕ) (Polynomial.X * Q), add_pow (Polynomial.X * Q) 1 β,
    Finset.mul_sum, Polynomial.finset_sum_coeff]
  simp_rw [hL]
  show ∑ i ∈ Finset.range (β + 1),
      (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i).coeff m * β.choose i =
    ∑ i ∈ Finset.range (m + 1),
      (((1 + Polynomial.X : Polynomial ℕ) ^ ρ) * (Polynomial.X * Q) ^ i).coeff m * β.choose i
  rw [Finset.sum_subset (Finset.range_mono (show β + 1 ≤ β + m + 1 by omega))
      (fun i _ hi => by
        rw [Finset.mem_range, not_lt] at hi
        rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]),
    Finset.sum_subset (Finset.range_mono (show m + 1 ≤ β + m + 1 by omega))
      (fun i _ hi => by
        rw [Finset.mem_range, not_lt] at hi
        rw [hz i (by omega), zero_mul])]
end Formalism.MainNotions.PlaneGram
