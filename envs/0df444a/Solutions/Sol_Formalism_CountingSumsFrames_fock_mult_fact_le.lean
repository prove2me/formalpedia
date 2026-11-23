-- Prove2me | solution 1 for Formalism.CountingSumsFrames.fock_mult_fact_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:34.764799+00:00
-- url     : https://prove2.me/submissions/62709f11-f7f9-4381-a893-919660359be9

import Definitions.Def_Formalism_PolynomialDimension_FrameSum
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_FockGaussComparisonHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Finset
open Formalism Formalism.CountingSumsFrames
namespace Formalism.CountingSumsFrames
theorem _root_.solution {α : Type*} (p : ℕ) (f : α → ℕ) (s : Finset α) :
    (Nat.multinomial s f).factorization p ≤ s.card * Nat.log p (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Nat.multinomial_insert ha, Nat.factorization_mul (Nat.choose_pos (Nat.le_add_right _ _)).ne'
    (Nat.multinomial_pos _ _).ne', Finsupp.add_apply, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
  have h1 := Nat.factorization_choose_le_log (p := p) (n := f a + ∑ i ∈ s, f i) (k := f a)
  have h2 : Nat.log p (∑ i ∈ s, f i) ≤ Nat.log p (f a + ∑ i ∈ s, f i) :=
    Nat.log_mono_right (Nat.le_add_left _ _)
  have h3 := Nat.mul_le_mul_left s.card h2
  rw [add_one_mul]
  omega
end Formalism.CountingSumsFrames
