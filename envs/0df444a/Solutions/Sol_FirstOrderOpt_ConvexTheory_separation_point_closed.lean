-- Prove2me | solution 1 for FirstOrderOpt.ConvexTheory.separation_point_closed
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:03:16.082987+00:00
-- url     : https://prove2.me/submissions/9b65d45d-ba68-42a9-ac86-0246560ec1c4

import Mathlib

set_option autoImplicit false

open scoped RealInnerProductSpace in
theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXne : X.Nonempty) (hXclosed : IsClosed X) (hXconv : Convex ℝ X)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∉ X) :
    ∃ w : EuclideanSpace ℝ (Fin n), w ≠ 0 ∧ ∀ x ∈ X, ⟪w, y⟫ < ⟪w, x⟫ := by
  obtain ⟨φ, u, hφy, hφX⟩ := geometric_hahn_banach_point_closed hXconv hXclosed hy
  have key : ∀ v : EuclideanSpace ℝ (Fin n),
      ⟪(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm φ, v⟫ = φ v :=
    fun v => InnerProductSpace.toDual_symm_apply
  refine ⟨(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm φ, ?_, fun x hx => ?_⟩
  · intro h0
    obtain ⟨x0, hx0⟩ := hXne
    have h1 := hφX x0 hx0
    have e1 := key y
    have e2 := key x0
    rw [h0, inner_zero_left] at e1 e2
    linarith
  · rw [key, key]
    linarith [hφX x hx]
