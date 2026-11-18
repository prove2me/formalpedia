-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_disjoint_union_probability_functional_finite_product_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:41:06.599547+00:00
-- url     : https://prove2.me/submissions/62df5c62-ec2f-4350-88b0-215a9dee652d

import Theorems.Thm_AvramDividend_Classical_avram_a27_admissible_disjoint_union_functional_finite_product_20261117
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped BigOperators
noncomputable section

/-- Multiplicativity on disjoint unions yields a finite disjoint-product formula. -/
theorem solution
    {α ι : Type*} [DecidableEq ι]
    (B : ι → Set α) (Q : Set α → ℝ)
    (hZero : Q ∅ = 1)
    (hMul : ∀ U V : Set α, Disjoint U V →
      Q (U ∪ V) = Q U * Q V) :
    ∀ S : Finset ι,
      (∀ i ∈ S, ∀ j ∈ S, i ≠ j →
        Disjoint (B i) (B j)) →
      Q (⋃ i ∈ S, B i) = ∏ i ∈ S, Q (B i) := by
  intro S hPair
  exact
    avram_a27_admissible_disjoint_union_functional_finite_product_20261117
      (fun _ : Set α => True) B Q hZero
      (by intro T hT; trivial)
      (by intro U V hU hV hDisj; exact hMul U V hDisj)
      S (by intro i hi; trivial) hPair
