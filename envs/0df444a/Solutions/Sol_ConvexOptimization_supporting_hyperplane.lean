-- Prove2me | solution 1 for ConvexOptimization.supporting_hyperplane
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T03:26:24.960097+00:00
-- url     : https://prove2.me/submissions/af76a815-4f92-4d56-b05a-d21ba481eb61

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem solution {n : ℕ}
    (C : Set (EuclideanSpace ℝ (Fin n))) (hC : Convex ℝ C)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : x₀ ∈ frontier C) :
    ∃ a : EuclideanSpace ℝ (Fin n), a ≠ 0 ∧ ∀ x ∈ C, ⟪a, x⟫ ≤ ⟪a, x₀⟫ := by
  have hx₀cl : x₀ ∈ closure C := hx₀.1
  have hx₀int : x₀ ∉ interior C := hx₀.2
  by_cases hint : (interior C).Nonempty
  · -- `C` has interior: separate the open convex set `interior C` from the point `x₀`
    -- by Hahn–Banach, then pass to the closure.
    obtain ⟨L, hL⟩ := geometric_hahn_banach_open_point hC.interior isOpen_interior hx₀int
    refine ⟨(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm L, ?_, ?_⟩
    · intro h
      obtain ⟨y, hy⟩ := hint
      have hL0 : L = 0 := by
        have := congrArg (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) h
        simpa using this
      rw [hL0] at hL
      simpa using hL y hy
    · intro x hx
      have hxcl : x ∈ closure (interior C) := by
        rw [hC.closure_interior_eq_closure_of_nonempty_interior hint]
        exact subset_closure hx
      have hclosed : IsClosed {z : EuclideanSpace ℝ (Fin n) | L z ≤ L x₀} :=
        isClosed_le L.continuous continuous_const
      have hsub : interior C ⊆ {z : EuclideanSpace ℝ (Fin n) | L z ≤ L x₀} :=
        fun z hz => le_of_lt (hL z hz)
      have hres : x ∈ {z : EuclideanSpace ℝ (Fin n) | L z ≤ L x₀} :=
        (hclosed.closure_subset_iff.mpr hsub) hxcl
      simpa [InnerProductSpace.toDual_symm_apply] using hres
  · -- `C` has empty interior: it lies in a proper affine subspace, and any normal
    -- to that subspace works — with equality rather than strict inequality.
    rw [Set.not_nonempty_iff_eq_empty] at hint
    rcases Set.eq_empty_or_nonempty C with rfl | hCne
    · simp [frontier] at hx₀
    · have hspanNe : ((affineSpan ℝ C : AffineSubspace ℝ (EuclideanSpace ℝ (Fin n))) :
          Set (EuclideanSpace ℝ (Fin n))).Nonempty :=
        hCne.mono (subset_affineSpan ℝ C)
      have hspan : affineSpan ℝ C ≠ ⊤ := by
        intro h
        have := (hC.interior_nonempty_iff_affineSpan_eq_top).mpr h
        rw [hint] at this
        exact absurd this (by simp)
      have hdir : (affineSpan ℝ C).direction ≠ ⊤ := by
        rw [Ne, AffineSubspace.direction_eq_top_iff_of_nonempty hspanNe]
        exact hspan
      have hperp : ((affineSpan ℝ C).direction)ᗮ ≠ ⊥ := by
        rw [Ne, Submodule.orthogonal_eq_bot_iff]
        exact hdir
      obtain ⟨a, ha, hane⟩ := Submodule.ne_bot_iff _ |>.mp hperp
      refine ⟨a, hane, ?_⟩
      intro x hx
      have hxs : x ∈ affineSpan ℝ C := subset_affineSpan ℝ C hx
      have hx₀s : x₀ ∈ affineSpan ℝ C :=
        ((AffineSubspace.closed_of_finiteDimensional
          (affineSpan ℝ C)).closure_subset_iff.mpr (subset_affineSpan ℝ C)) hx₀cl
      have hvsub : x - x₀ ∈ (affineSpan ℝ C).direction :=
        AffineSubspace.vsub_mem_direction hxs hx₀s
      have h0 : ⟪x - x₀, a⟫ = 0 := (Submodule.mem_orthogonal _ _).mp ha _ hvsub
      have h0' : ⟪a, x - x₀⟫ = 0 := by rw [real_inner_comm]; exact h0
      rw [inner_sub_right, sub_eq_zero] at h0'
      exact le_of_eq h0'
