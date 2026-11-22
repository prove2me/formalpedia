-- Prove2me | solution 1 for Formalism.CountingSumsFrames.Har4.multinomial_factorization_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:36:05.962377+00:00
-- url     : https://prove2.me/submissions/1087f48d-df38-4b0b-a674-785216cbcf7e

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_DiagLaplacianDivPowMemSqrtFockLattice
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_SqrtFockGaussLatticeComparisonHolds

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
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Formalism.CountingSumsFrames.Har4
namespace Formalism.CountingSumsFrames.Har4
theorem _root_.solution (p : ℕ) {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) :
    (Nat.multinomial s f).factorization p ≤ (s.card - 1) * Nat.log p (∑ i ∈ s, f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      simp [Nat.multinomial_singleton]
    · rw [Nat.multinomial_insert ha, Finset.sum_insert ha, Finset.card_insert_eq_ite, if_neg ha]
      have hc : (f a + ∑ i ∈ s, f i).choose (f a) ≠ 0 := (Nat.choose_pos (Nat.le_add_right _ _)).ne'
      have hm : Nat.multinomial s f ≠ 0 := (Nat.multinomial_pos _ _).ne'
      rw [Nat.factorization_mul hc hm, Finsupp.add_apply]
      have h1 : ((f a + ∑ i ∈ s, f i).choose (f a)).factorization p ≤ Nat.log p (f a + ∑ i ∈ s, f i) :=
        Nat.factorization_choose_le_log
      have h2 : Nat.log p (∑ i ∈ s, f i) ≤ Nat.log p (f a + ∑ i ∈ s, f i) :=
        Nat.log_mono_right (Nat.le_add_left _ _)
      have hcard : 1 ≤ s.card := hs.card_pos
      calc ((f a + ∑ i ∈ s, f i).choose (f a)).factorization p + (Nat.multinomial s f).factorization p
          ≤ Nat.log p (f a + ∑ i ∈ s, f i) + (s.card - 1) * Nat.log p (f a + ∑ i ∈ s, f i) :=
            add_le_add h1 (le_trans ih (Nat.mul_le_mul_left _ h2))
        _ = (s.card + 1 - 1) * Nat.log p (f a + ∑ i ∈ s, f i) := by
            have e : s.card + 1 - 1 = (s.card - 1) + 1 := by omega
            rw [e, add_mul, one_mul, add_comm]
end Formalism.CountingSumsFrames.Har4
