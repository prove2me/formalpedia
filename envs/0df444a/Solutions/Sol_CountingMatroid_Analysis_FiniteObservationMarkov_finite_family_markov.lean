-- Prove2me | solution 1 for CountingMatroid.Analysis.FiniteObservationMarkov.finite_family_markov
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T14:12:48.018611+00:00
-- url     : https://prove2.me/submissions/418e98af-8f0a-46bb-a0a3-f24f9c297116

import Definitions.Def_CountingMatroid_Analysis_RelativeObservationBounds
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List
import Mathlib.Tactic
import Theorems.Thm_CountingMatroid_Analysis_FiniteObservationMarkov_finite_markov_card

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteObservationMarkov
end CountingMatroid.Analysis.FiniteObservationMarkov
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteObservationMarkov

open CountingMatroid.Analysis.RelativeObservationBounds

/-- INTERNAL: Markov and the finite observable union bound, expressed using
masked second moments rather than an independence claim about observations.
TEXLINE: main.tex:1253-1266 -/
theorem solution {α β : Type} [Fintype α] [Fintype β]
    (bad : α → Prop) (error : α → β → ℚ) (weight threshold bound : ℚ)
    (hweight : 0 ≤ weight) (hthreshold : 0 < threshold)
    (herror : ∀ x i, 0 ≤ error x i)
    (hbad : ∀ x, bad x → ∃ i, threshold ≤ error x i)
    (hmoment : ∀ i, (∑ x, error x i) * weight ≤ bound) :
    letI := Classical.propDecidable
    ((Finset.univ.filter bad).card : ℚ) * weight ≤
      (Fintype.card β : ℚ) * bound / threshold := by
  classical
  have hmarkov := finite_markov_card bad (fun x => ∑ i, error x i) threshold
    (fun x => Finset.sum_nonneg (fun i _ => herror x i)) (by
      intro x hx
      obtain ⟨i, hi⟩ := hbad x hx
      exact hi.trans (Finset.single_le_sum (fun k _ => herror x k) (Finset.mem_univ i)))
  have htotal : (∑ x, ∑ i, error x i) * weight ≤ (Fintype.card β : ℚ) * bound := by
    rw [Finset.sum_comm, Finset.sum_mul]
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hmoment i)
  apply (le_div_iff₀ hthreshold).mpr
  have hweighted := mul_le_mul_of_nonneg_right hmarkov hweight
  nlinarith
