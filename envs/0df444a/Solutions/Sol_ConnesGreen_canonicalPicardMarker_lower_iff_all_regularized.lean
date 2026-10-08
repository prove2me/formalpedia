-- Prove2me | solution 1 for ConnesGreen.canonicalPicardMarker_lower_iff_all_regularized
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T00:00:23.616009+00:00
-- url     : https://prove2.me/submissions/d3302b8f-ef04-4511-abf9-9a65b93b9a38

import Definitions.Def_ConnesGreen_RG0_original_inner_marker
open ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect.MarkerStability
open scoped InnerProductSpace lp Classical ComplexOrder Topology
open Filter Set
set_option autoImplicit false
noncomputable section
theorem solution
    (t : ℝ) (ht : 0 < t) (S : Finset CriticalZeros) (a : ℝ) :
    a • (1 : ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ) →L[ℂ]
      ℓ²({ρ : CriticalZeros // ρ ∈ S}, ℂ)) ≤ canonicalPicardMarker t ht S ↔
    ∀ ε : ℝ, 0 < ε → a • 1 ≤ canonicalRegularizedMarker t ht S ε := by
  constructor
  · intro h ε hε
    exact h.trans ((canonicalPicardMarker_spec t ht S).2.2.1.1 ⟨ε, hε, rfl⟩)
  · intro h
    apply (canonicalPicardMarker_spec t ht S).2.2.1.2
    rintro _ ⟨ε, hε, rfl⟩
    exact h ε hε

