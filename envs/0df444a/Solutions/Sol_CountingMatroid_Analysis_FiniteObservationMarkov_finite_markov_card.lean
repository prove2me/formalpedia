-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteObservationMarkov.finite_markov_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:06:24.393169+00:00
-- url     : https://prove2.me/submissions/f20a6671-54bd-4fb7-a9af-37fab75a6c35

import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteObservationMarkov

open CountingMatroid.Analysis.RelativeObservationBounds

/-- INTERNAL: Discrete Markov inequality with no independence hypothesis.
The error can be a masked squared deviation on successful executions.
TEXLINE: main.tex:1253-1266 -/
theorem solution {α : Type} [Fintype α] (bad : α → Prop)
    (error : α → ℚ) (threshold : ℚ)
    (herror : ∀ x, 0 ≤ error x) (hbad : ∀ x, bad x → threshold ≤ error x) :
    letI := Classical.propDecidable
    ((Finset.univ.filter bad).card : ℚ) * threshold ≤ ∑ x, error x := by
  classical
  calc
    ((Finset.univ.filter bad).card : ℚ) * threshold =
        ∑ _x ∈ Finset.univ.filter bad, threshold := by simp
    _ ≤ ∑ x ∈ Finset.univ.filter bad, error x := by
      apply Finset.sum_le_sum
      intro x hx
      exact hbad x (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x, error x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => herror x)
