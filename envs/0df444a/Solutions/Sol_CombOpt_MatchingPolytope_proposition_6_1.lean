-- Prove2me | solution 1 for CombOpt.MatchingPolytope.proposition_6_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T19:51:25.276193+00:00
-- url     : https://prove2.me/submissions/dc277406-ce1b-433e-b1a5-3def221d9cf0

import Mathlib

theorem solution {ι : Type*} [Fintype ι] (S : Set (ι → ℝ)) (hS : S.Finite)
    (hne : S.Nonempty) (w : ι → ℝ) :
    ∃ m : ℝ, IsGreatest ((fun x => w ⬝ᵥ x) '' S) m ∧
      IsGreatest ((fun x => w ⬝ᵥ x) '' convexHull ℝ S) m := by
  obtain ⟨x, hx, hmax⟩ := Set.exists_max_image S (fun x => w ⬝ᵥ x) hS hne
  refine ⟨w ⬝ᵥ x, ⟨⟨x, hx, rfl⟩, ?_⟩, ⟨⟨x, subset_convexHull ℝ S hx, rfl⟩, ?_⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hmax y hy
  · have hlin : IsLinearMap ℝ (fun y : ι → ℝ => w ⬝ᵥ y) :=
      ⟨fun a b => dotProduct_add w a b, fun c a => dotProduct_smul c w a⟩
    have hsub : convexHull ℝ S ⊆ {y | w ⬝ᵥ y ≤ w ⬝ᵥ x} :=
      convexHull_min (fun y hy => hmax y hy) (convex_halfSpace_le hlin _)
    rintro _ ⟨y, hy, rfl⟩
    exact hsub hy
