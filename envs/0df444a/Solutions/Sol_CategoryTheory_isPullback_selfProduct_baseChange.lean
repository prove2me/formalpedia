-- Prove2me | solution 1 for CategoryTheory.isPullback_selfProduct_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:04:40.393178+00:00
-- url     : https://prove2.me/submissions/41d2622e-4786-47fe-8663-9b4a58a258f8

import Mathlib

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The self-product of a base change is the base change of the self-product. -/
theorem _root_.solution {C : Type*} [Category C] [HasPullbacks C]
    {X S T : C} (f : X ⟶ S) (b : T ⟶ S) :
    IsPullback
      (pullback.map (pullback.snd f b) (pullback.snd f b) f f
        (pullback.fst f b) (pullback.fst f b) b pullback.condition.symm pullback.condition.symm)
      (pullback.fst (pullback.snd f b) (pullback.snd f b) ≫ pullback.snd f b)
      (pullback.fst f f ≫ f) b := by
  let f' := pullback.snd f b
  let g := pullback.fst f b
  let π := pullback.map f' f' f f g g b pullback.condition.symm pullback.condition.symm
  have h : IsPullback π (pullback.snd f' f') (pullback.snd f f) g :=
    IsPullback.paste_twist_right (IsPullback.of_hasPullback f b) (IsPullback.of_hasPullback f f)
      f' g pullback.condition.symm (pullback.fst f' f') (pullback.snd f' f')
      (IsPullback.of_hasPullback f' f')
      (by simp only [π, pullback.map, pullback.lift_fst]; rfl)
      (by simp only [π, pullback.map, pullback.lift_snd])
  have hp := h.paste_vert (IsPullback.of_hasPullback f b)
  have h₁ : pullback.snd f' f' ≫ f' = pullback.fst f' f' ≫ f' := pullback.condition.symm
  have h₂ : pullback.snd f f ≫ f = pullback.fst f f ≫ f := pullback.condition.symm
  rw [h₁, h₂] at hp
  exact hp

end CategoryTheory
