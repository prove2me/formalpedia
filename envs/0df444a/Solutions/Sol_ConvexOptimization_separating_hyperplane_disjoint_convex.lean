-- Prove2me | solution 1 for ConvexOptimization.separating_hyperplane_disjoint_convex
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-08-12T20:17:58.418347+00:00
-- url     : https://prove2.me/submissions/5963698d-2b2e-487d-b1f5-c5946f150399

import Mathlib

open scoped RealInnerProductSpace ENNReal Pointwise
open MeasureTheory

theorem solution {n : ℕ}
    (C D : Set (EuclideanSpace ℝ (Fin n)))
    (hC : Convex ℝ C) (hD : Convex ℝ D)
    (hCne : C.Nonempty) (hDne : D.Nonempty) (hdisj : Disjoint C D) :
    ∃ a : EuclideanSpace ℝ (Fin n), a ≠ 0 ∧ ∃ b : ℝ,
      (∀ x ∈ C, ⟪a, x⟫ ≤ b) ∧ (∀ x ∈ D, b ≤ ⟪a, x⟫) := by
  classical
  -- the difference set: convex, nonempty, avoiding the origin
  have hEconv : Convex ℝ (C - D) := hC.sub hD
  have hEne : (C - D).Nonempty := by
    obtain ⟨c₀, hc₀⟩ := hCne
    obtain ⟨d₀, hd₀⟩ := hDne
    exact ⟨c₀ - d₀, Set.sub_mem_sub hc₀ hd₀⟩
  have h0E : (0 : EuclideanSpace ℝ (Fin n)) ∉ C - D := by
    intro h0
    rcases Set.mem_sub.mp h0 with ⟨c, hc, d, hd, hcd⟩
    have hcd' : c = d := sub_eq_zero.mp hcd
    rw [hcd'] at hc
    exact (Set.disjoint_left.mp hdisj hc) hd
  -- a nonzero functional that is nonpositive on the difference set
  have key : ∃ a : EuclideanSpace ℝ (Fin n), a ≠ 0 ∧ ∀ e ∈ C - D, ⟪a, e⟫ ≤ 0 := by
    by_cases hspan : affineSpan ℝ (C - D) = ⊤
    · -- full-dimensional case: the difference set has nonempty interior,
      -- separate it from the origin by Hahn–Banach
      have hint : (interior (C - D)).Nonempty :=
        hEconv.interior_nonempty_iff_affineSpan_eq_top.mpr hspan
      have hdisj0 : Disjoint (interior (C - D))
          ({0} : Set (EuclideanSpace ℝ (Fin n))) := by
        rw [Set.disjoint_singleton_right]
        exact fun h => h0E (interior_subset h)
      obtain ⟨f, u, hfne, hfE, hf0⟩ :=
        geometric_hahn_banach_of_nonempty_interior hEconv (convex_singleton 0)
          hdisj0 hint (Set.singleton_nonempty 0)
      have hu0 : u ≤ 0 := by
        have h1 := hf0 0 (Set.mem_singleton 0)
        simpa using h1
      refine ⟨(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm f, ?_, ?_⟩
      · intro ha0
        apply hfne
        have h2 := (InnerProductSpace.toDual ℝ
          (EuclideanSpace ℝ (Fin n))).apply_symm_apply f
        rw [← h2, ha0, map_zero]
      · intro e he
        rw [InnerProductSpace.toDual_symm_apply]
        exact le_trans (hfE e he) hu0
    · -- lower-dimensional case: a direction orthogonal to the affine span
      -- makes the functional constant on the difference set
      have hEspanne : (affineSpan ℝ (C - D) :
          Set (EuclideanSpace ℝ (Fin n))).Nonempty := by
        obtain ⟨e, he⟩ := hEne
        exact ⟨e, subset_affineSpan ℝ (C - D) he⟩
      have hdir : (affineSpan ℝ (C - D)).direction ≠ ⊤ := by
        intro hdir
        exact hspan
          ((AffineSubspace.direction_eq_top_iff_of_nonempty hEspanne).mp hdir)
      have hbot : ((affineSpan ℝ (C - D)).direction)ᗮ ≠ ⊥ := by
        intro hbot
        exact hdir (Submodule.orthogonal_eq_bot_iff.mp hbot)
      obtain ⟨a, hamem, hane⟩ := Submodule.ne_bot_iff _ |>.mp hbot
      obtain ⟨e₀, he₀⟩ := hEne
      have hconst : ∀ e ∈ C - D, ⟪a, e⟫ = ⟪a, e₀⟫ := by
        intro e he
        have hsub : e - e₀ ∈ (affineSpan ℝ (C - D)).direction := by
          have h1 := AffineSubspace.vsub_mem_direction
            (subset_affineSpan ℝ (C - D) he) (subset_affineSpan ℝ (C - D) he₀)
          simpa using h1
        have h2 : ⟪e - e₀, a⟫ = 0 :=
          (Submodule.mem_orthogonal _ a).mp hamem (e - e₀) hsub
        have h3 : ⟪a, e - e₀⟫ = 0 := by
          rw [real_inner_comm]
          exact h2
        rw [inner_sub_right] at h3
        linarith
      rcases le_total ⟪a, e₀⟫ 0 with hk | hk
      · exact ⟨a, hane, fun e he => by rw [hconst e he]; exact hk⟩
      · refine ⟨-a, neg_ne_zero.mpr hane, fun e he => ?_⟩
        rw [inner_neg_left, hconst e he]
        linarith
  obtain ⟨a, hane, ha⟩ := key
  -- the functional is dominated on `C` by its values on `D`
  have hcd : ∀ c ∈ C, ∀ d ∈ D, ⟪a, c⟫ ≤ ⟪a, d⟫ := by
    intro c hc d hd
    have h1 : c - d ∈ C - D := Set.sub_mem_sub hc hd
    have h2 := ha _ h1
    rw [inner_sub_right] at h2
    linarith
  obtain ⟨d₀, hd₀⟩ := hDne
  have hbdd : BddAbove ((fun x => ⟪a, x⟫) '' C) := by
    refine ⟨⟪a, d₀⟫, ?_⟩
    rintro y ⟨c, hc, rfl⟩
    exact hcd c hc d₀ hd₀
  refine ⟨a, hane, sSup ((fun x => ⟪a, x⟫) '' C), fun c hc => ?_, fun d hd => ?_⟩
  · exact le_csSup hbdd ⟨c, hc, rfl⟩
  · refine csSup_le (hCne.image _) ?_
    rintro y ⟨c, hc, rfl⟩
    exact hcd c hc d hd
