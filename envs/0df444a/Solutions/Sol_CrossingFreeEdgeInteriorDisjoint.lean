-- Prove2me | solution 1 for CrossingFreeEdgeInteriorDisjoint
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-27T19:43:35.421237+00:00
-- url     : https://prove2.me/submissions/1a31115d-79d6-4bd1-ade0-19fa545af039

import Definitions.Def_OrdinaryPolygonalDrawing

open Classical
noncomputable section

theorem solution {V : Type*} [Fintype V]
    (G : SimpleGraph V) [Fintype G.edgeSet]
    (D : OrdinaryPolygonalDrawing G) (hD : D.crossingSet.card = 0) :
    ∀ ⦃e₁ e₂ : G.edgeFinset⦄ ⦃p : EuclideanSpace ℝ (Fin 2)⦄,
      e₁ ≠ e₂ →
        p ∈ (D.edgeArc e₁).relativeInterior →
          p ∈ (D.edgeArc e₂).relativeInterior → False := by
  intro e₁ e₂ p hne hp₁ hp₂
  have hp_cross : p ∈ D.crossingSet := by
    rw [D.crossingSet_spec]
    exact ⟨e₁, e₂, hne, hp₁, hp₂⟩
  have h_empty : D.crossingSet = ∅ := Finset.card_eq_zero.mp hD
  have h_not : p ∉ D.crossingSet := by
    simp [h_empty]
  exact h_not hp_cross
