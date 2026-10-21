-- Prove2me | solution 1 for EquiSegment.Multivalued.eq_4_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:47:21.276354+00:00
-- url     : https://prove2.me/submissions/3a0f2229-6b86-49da-b7f4-8f7ddf0daf65

import Mathlib
import Definitions.Def_EquiSegment_Multivalued_Setting

set_option autoImplicit false
open EquiSegment.Multivalued

theorem solution (φ : ℝ × ℝ → ℝ → ℝ) (p : ℕ)
    (hp : p.Prime) (hφ : IsRep φ) (hdeg : DegId φ) :
    ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      (((a, a), y) ∈ projZ φ p ↔ y = 0) := by
  intro a ha y hy
  have hp0 : 0 < p := hp.pos
  constructor
  · rintro ⟨_, x, hmono, h0, hlast, hz⟩
    have hx : ∀ i, x i = a := by
      intro i
      apply le_antisymm
      · calc x i ≤ x (Fin.last p) := hmono (Fin.le_last i)
          _ = a := hlast
      · calc a = x 0 := h0.symm
          _ ≤ x i := hmono (Fin.zero_le i)
    have h := hz ⟨0, hp0⟩
    rw [hx, hx, hdeg a ha y hy] at h
    exact h
  · rintro rfl
    refine ⟨⟨⟨ha.1, le_refl _, ha.2⟩, hy⟩, fun _ => a, monotone_const, rfl, rfl, fun i => ?_⟩
    exact hdeg a ha 0 hy
