-- Prove2me | solution 1 for ConvexOptAlg.ProjectedGD.lemma_3_1_pythagoras
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T17:23:40.065517+00:00
-- url     : https://prove2.me/submissions/9aabb217-d760-4731-a1ab-bdba8ad4040b

import Mathlib
import Definitions.Def_OnlineConvexOpt_FirstOrder_Protocol

open OnlineConvexOpt.FirstOrder

theorem pgd9dc_inner_le {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (X : Set F) (hXcv : Convex ℝ X) (x y p : F) (hx : x ∈ X) (hpX : p ∈ X)
    (hmin : ∀ z ∈ X, ‖y - p‖ ≤ ‖y - z‖) :
    inner ℝ (y - p) (x - p) ≤ 0 := by
  have hnorm : ‖y - p‖ = ⨅ w : X, ‖y - (w : F)‖ := by
    have hne : Nonempty X := ⟨⟨p, hpX⟩⟩
    have hbdd : BddBelow (Set.range fun w : X => ‖y - (w : F)‖) :=
      ⟨0, Set.forall_mem_range.2 fun w => norm_nonneg _⟩
    apply le_antisymm
    · exact le_ciInf fun w => hmin w w.2
    · exact ciInf_le hbdd (⟨p, hpX⟩ : X)
  exact (norm_eq_iInf_iff_real_inner_le_zero hXcv hpX).1 hnorm x hx

theorem pgd9dc_pyth {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (a b : F) (h : inner ℝ a b ≤ 0) : ‖b‖ ^ 2 + ‖a‖ ^ 2 ≤ ‖a - b‖ ^ 2 := by
  have := norm_sub_sq_real a b
  rw [this]
  linarith

open OnlineConvexOpt.FirstOrder in
theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (x y p : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (hp : IsMetricProjection X y p) :
    ‖p - x‖ ^ 2 + ‖y - p‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by
  obtain ⟨hpX, hmin⟩ := hp
  have hmin' : ∀ z ∈ X, ‖y - p‖ ≤ ‖y - z‖ := fun z hz => by
    have := hmin z hz
    rwa [dist_eq_norm, dist_eq_norm] at this
  have h := pgd9dc_inner_le X hXcv x y p hx hpX hmin'
  have key := pgd9dc_pyth (y - p) (x - p) h
  have e : y - p - (x - p) = y - x := by abel
  have e2 : ‖x - p‖ = ‖p - x‖ := norm_sub_rev x p
  rw [e, e2] at key
  exact key
