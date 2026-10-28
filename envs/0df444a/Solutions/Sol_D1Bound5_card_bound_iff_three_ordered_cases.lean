-- Prove2me | solution 1 for D1Bound5.card_bound_iff_three_ordered_cases
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T21:28:15.881194+00:00
-- url     : https://prove2.me/submissions/a7c68309-e3a2-4452-8e76-5f5d9f90bdd4

import Definitions.Def_D1Bound5_IsD1
import Definitions.Def_D1Bound5_IsD1Tuple
import Definitions.Def_D1Bound5_MainStatement
import Mathlib.Analysis.Complex.Basic
import Lean.Elab.Tactic.Omega
import Theorems.Thm_D1Bound5_card_bound_iff_no_ordered_sextuple
open scoped NumberField
universe u

namespace D1Bound5

theorem _root_.solution
    {R W : Type*} [CommRing R] [LinearOrder W]
    (weight : R → W) (cutoff : W) :
    (∀ A : Finset R, IsD1 A → A.card ≤ 5) ↔
      (∀ t : Fin 6 → R, IsD1Tuple t → Monotone (weight ∘ t) →
        cutoff ≤ weight (t 0) → False) ∧
      (∀ t : Fin 6 → R, IsD1Tuple t → Monotone (weight ∘ t) →
        weight (t 0) < cutoff → cutoff ≤ weight (t 1) → False) ∧
      (∀ t : Fin 6 → R, IsD1Tuple t → Monotone (weight ∘ t) →
        weight (t 1) < cutoff → False) := by
  rw [card_bound_iff_no_ordered_sextuple weight]
  constructor
  · intro h
    exact ⟨fun t ht hm _ => h t ht hm,
      fun t ht hm _ _ => h t ht hm,
      fun t ht hm _ => h t ht hm⟩
  · rintro ⟨hlarge, hone, htwo⟩ t ht hm
    by_cases hfirst : cutoff ≤ weight (t 0)
    · exact hlarge t ht hm hfirst
    · by_cases hsecond : cutoff ≤ weight (t 1)
      · exact hone t ht hm (lt_of_not_ge hfirst) hsecond
      · exact htwo t ht hm (lt_of_not_ge hsecond)

end D1Bound5
