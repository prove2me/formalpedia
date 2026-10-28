-- Prove2me | solution 1 for FunctionalInequalities.Analysis.Semigroup.Generated.continuousOn_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:27:56.403489+00:00
-- url     : https://prove2.me/submissions/45215b8b-181f-4ca1-855e-eb83f56649af

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Semigroup_Generated_Laws

noncomputable section
open InnerProductSpace
open scoped RealInnerProductSpace
variable {H₀ H₁ : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
/-- **`P8`**: `t ↦ P_t f` is continuous on `[0, ∞)`.  For `t₀ ≤ t` the semigroup law gives
`P_t f - P_{t₀} f = P_{t₀} (P_{t - t₀} f - f)`, which the contraction contraction bounds by
`‖P_{t - t₀} f - f‖`; for `t ≤ t₀` exchange the roles.  Then apply `P7`. -/
theorem solution (T : H₀ →ₗ.[ℝ] H₁) (hT : T.IsClosed)
    (hd : Dense (T.domain : Set H₀)) (f : H₀) :
    ContinuousOn (fun t : ℝ => FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f) (Set.Ici 0) := by
  rw [Metric.continuousOn_iff]
  intro t₀ ht₀ ε hε
  obtain ⟨δ, hδ, h⟩ := FunctionalInequalities.Analysis.Semigroup.Generated.continuous_at_zero T hT hd f hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht hdist
  simp only [Set.mem_Ici] at ht ht₀
  rw [Real.dist_eq] at hdist
  obtain ⟨hlow, hhigh⟩ := abs_lt.mp hdist
  simp only [dist_eq_norm]
  rcases le_total t₀ t with hle | hle
  · have hsum : t₀ + (t - t₀) = t := by ring
    have hsplit : FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t f
        = FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t₀ (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd (t - t₀) f) := by
      rw [← FunctionalInequalities.Analysis.Semigroup.Generated.add_time T hT hd ht₀ (by linarith : (0 : ℝ) ≤ t - t₀), hsum]
    rw [hsplit, ← FunctionalInequalities.Analysis.Semigroup.Generated.map_sub T hT hd ht₀]
    exact lt_of_le_of_lt (FunctionalInequalities.Analysis.Semigroup.Generated.norm_apply_le T hT hd ht₀ _)
      (h (t - t₀) (by linarith) (by linarith))
  · have hsum : t + (t₀ - t) = t₀ := by ring
    have hsplit : FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t₀ f
        = FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd t (FunctionalInequalities.Analysis.Semigroup.Generated.apply T hT hd (t₀ - t) f) := by
      rw [← FunctionalInequalities.Analysis.Semigroup.Generated.add_time T hT hd ht (by linarith : (0 : ℝ) ≤ t₀ - t), hsum]
    rw [hsplit, ← FunctionalInequalities.Analysis.Semigroup.Generated.map_sub T hT hd ht]
    refine lt_of_le_of_lt (FunctionalInequalities.Analysis.Semigroup.Generated.norm_apply_le T hT hd ht _) ?_
    rw [norm_sub_rev]
    exact h (t₀ - t) (by linarith) (by linarith)
