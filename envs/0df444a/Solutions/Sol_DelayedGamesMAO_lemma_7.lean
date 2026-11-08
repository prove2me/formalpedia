-- Prove2me | solution 1 for DelayedGamesMAO.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:11:04.017749+00:00
-- url     : https://prove2.me/submissions/a898003e-0220-423f-b5cc-21e7aee610ac

import Mathlib
import Definitions.Def_DelayedGamesMAO_newObs

set_option autoImplicit false

open DelayedGamesMAO in
theorem solution (T : ℕ) (hT : 1 ≤ T) (d : ℕ → ℕ) (hd : ∀ t ∈ Finset.Icc 1 T, t + d t ≤ T)
    (δ : ℕ → ℝ) (lam : ℕ → ℕ → ℝ) (hδ : ∀ t, 0 ≤ δ t) (hlam : ∀ t s, 0 ≤ lam t s) :
    ∑ t ∈ Finset.Icc 1 T, ∑ s ∈ newObs d t, lam (t + 1) s * δ s =
      ∑ t ∈ Finset.Icc 1 T, lam (t + d t + 1) t * δ t := by
  rw [Finset.sum_comm' (t' := Finset.Icc 1 T) (s' := fun s => {s + d s})]
  · exact Finset.sum_congr rfl (fun s _ => by rw [Finset.sum_singleton])
  · intro t s
    simp only [newObs, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
      exact ⟨h5.symm, h3, by omega⟩
    · rintro ⟨h5, h3, h4⟩
      have := hd s (Finset.mem_Icc.mpr ⟨h3, h4⟩)
      subst h5
      exact ⟨⟨by omega, by omega⟩, ⟨h3, by omega⟩, rfl⟩
