-- Prove2me | solution 1 for Formalism.MainNotions.G.SymmetricFormBlocks.assemble
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:40:21.947926+00:00
-- url     : https://prove2.me/submissions/065d23ca-b9fa-4221-85cc-b00c0ce5f8b9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialFactorials_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.G.SymmetricFormBlocks
open Finset
namespace Formalism.MainNotions.G.SymmetricFormBlocks
theorem _root_.solution {α ι Z : Type*} (A : Finset α) (Wn : Finset ℕ) (I : Finset Z) (T : Finset ι)
    (bl : α → ℕ → Z → ℝ) (bq : α → Z → ℝ) (dx : Z → ℝ) (dy : α → Z → ℝ) (u : α → ι → α) (m : α → ℝ)
    (ε₁ ε₂ K : ℝ) (h1 : 0 ≤ ε₁) (h2 : 0 ≤ ε₂) (hdx : ∀ z, 0 ≤ dx z)
    (hplus : ∀ a ∈ A, ∀ z ∈ I, ∑ w ∈ Wn, bl a w z ≤ (Wn.card : ℝ) * (bq a z * dx z + ε₂ * (dy a z * dx z)))
    (htm : ∀ z ∈ I, ∑ a ∈ A, bq a z ≤ ε₁ * ∑ i ∈ T, ∑ a ∈ A, dy (u a i) z)
    (hcnt : ∀ a ∈ A, ∑ z ∈ I, dy a z * dx z ≤ m a)
    (hu : ∀ a ∈ A, ∀ i ∈ T, u a i ∈ A ∧ m (u a i) ≤ K * m a) :
    ∑ a ∈ A, ∑ w ∈ Wn, ∑ z ∈ I, bl a w z ≤ (ε₁ * T.card * K + ε₂) * ((Wn.card : ℝ) * ∑ a ∈ A, m a) := by
  have hS1 : ∑ a ∈ A, ∑ w ∈ Wn, ∑ z ∈ I, bl a w z ≤
      ∑ a ∈ A, ∑ z ∈ I, (Wn.card : ℝ) * (bq a z * dx z + ε₂ * (dy a z * dx z)) := by
    apply Finset.sum_le_sum
    intro a ha
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun z hz => hplus a ha z hz
  have hQ : ∑ a ∈ A, ∑ z ∈ I, bq a z * dx z ≤ ε₁ * T.card * K * ∑ a ∈ A, m a := by
    calc ∑ a ∈ A, ∑ z ∈ I, bq a z * dx z = ∑ z ∈ I, ∑ a ∈ A, bq a z * dx z := Finset.sum_comm
      _ = ∑ z ∈ I, (∑ a ∈ A, bq a z) * dx z := by
          apply Finset.sum_congr rfl
          intro z _
          rw [Finset.sum_mul]
      _ ≤ ∑ z ∈ I, (ε₁ * ∑ i ∈ T, ∑ a ∈ A, dy (u a i) z) * dx z := by
          apply Finset.sum_le_sum
          intro z hz
          exact mul_le_mul_of_nonneg_right (htm z hz) (hdx z)
      _ = ∑ z ∈ I, ∑ i ∈ T, ∑ a ∈ A, ε₁ * (dy (u a i) z * dx z) := by
          apply Finset.sum_congr rfl
          intro z _
          rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul, Finset.mul_sum]
      _ = ∑ i ∈ T, ∑ z ∈ I, ∑ a ∈ A, ε₁ * (dy (u a i) z * dx z) := Finset.sum_comm
      _ = ∑ i ∈ T, ∑ a ∈ A, ∑ z ∈ I, ε₁ * (dy (u a i) z * dx z) :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ ≤ ∑ i ∈ T, ∑ a ∈ A, ε₁ * (K * m a) := by
          apply Finset.sum_le_sum
          intro i hi
          apply Finset.sum_le_sum
          intro a ha
          rw [← Finset.mul_sum]
          apply mul_le_mul_of_nonneg_left _ h1
          exact (hcnt (u a i) (hu a ha i hi).1).trans (hu a ha i hi).2
      _ = ∑ i ∈ T, ε₁ * (K * ∑ a ∈ A, m a) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum, Finset.mul_sum]
      _ = ε₁ * T.card * K * ∑ a ∈ A, m a := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  have hD : ∑ a ∈ A, ∑ z ∈ I, ε₂ * (dy a z * dx z) ≤ ε₂ * ∑ a ∈ A, m a := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hcnt a ha) h2
  calc ∑ a ∈ A, ∑ w ∈ Wn, ∑ z ∈ I, bl a w z
      ≤ ∑ a ∈ A, ∑ z ∈ I, (Wn.card : ℝ) * (bq a z * dx z + ε₂ * (dy a z * dx z)) := hS1
    _ = (Wn.card : ℝ) * (∑ a ∈ A, ∑ z ∈ I, bq a z * dx z
          + ∑ a ∈ A, ∑ z ∈ I, ε₂ * (dy a z * dx z)) := by
        simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ (Wn.card : ℝ) * (ε₁ * T.card * K * ∑ a ∈ A, m a + ε₂ * ∑ a ∈ A, m a) :=
        mul_le_mul_of_nonneg_left (add_le_add hQ hD) (Nat.cast_nonneg _)
    _ = (ε₁ * T.card * K + ε₂) * ((Wn.card : ℝ) * ∑ a ∈ A, m a) := by ring
end Formalism.MainNotions.G.SymmetricFormBlocks
