-- Prove2me | solution 1 for FunctionalInequalities.Analysis.affineMaximum_coercive_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:29:48.606789+00:00
-- url     : https://prove2.me/submissions/b841ff21-39f1-4672-9ea8-ddec1b4459a0

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_AffineMaximum

noncomputable section
open Filter Set
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The geometric neighborhood produces a linear lower bound for the actual
finite affine maximum. The intercept bound is only at its finitely many vertices. -/
theorem solution [FiniteDimensional ℝ E]
    (s : Finset E) (hs : s.Nonempty)
    (h0 : (0 : E) ∈ interior (convexHull ℝ (↑s : Set E))) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : E → ℝ) (M : ℝ), (∀ x ∈ s, a x ≤ M) →
      ∀ y, c * ‖y‖ - M ≤ FunctionalInequalities.Analysis.affineMaximum s hs a y := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (mem_interior_iff_mem_nhds.mp h0)
  refine ⟨r / 2, half_pos hr, ?_⟩
  intro a M ha y
  let A := FunctionalInequalities.Analysis.affineMaximum s hs a y
  have hvertices : (↑s : Set E) ⊆ {x | inner ℝ x y ≤ A + M} := by
    intro x hx
    change inner ℝ x y ≤ A + M
    have hmax := Finset.le_sup' (fun x => inner ℝ x y - a x) hx
    change inner ℝ x y - a x ≤ A at hmax
    have := ha x hx
    linarith
  have hhalf : Convex ℝ {x : E | inner ℝ x y ≤ A + M} := by
    intro x hx z hz α β hα hβ hsum
    simp only [mem_ofPred_eq, inner_add_left, inner_smul_left, starRingEnd_apply, star_trivial]
    have hh := add_le_add (mul_le_mul_of_nonneg_left hx hα)
      (mul_le_mul_of_nonneg_left hz hβ)
    rw [← add_mul, hsum, one_mul] at hh
    exact hh
  have hhull := convexHull_min hvertices hhalf
  by_cases hy : y = 0
  · subst y
    have hz : (0 : E) ∈ convexHull ℝ (↑s : Set E) := interior_subset h0
    have hh := hhull hz
    simp only [mem_ofPred_eq, inner_zero_right] at hh
    simpa only [norm_zero, mul_zero, zero_sub] using (by linarith : -M ≤ A)
  have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let z : E := (r / 2 / ‖y‖) • y
  have hz : z ∈ Metric.ball (0 : E) r := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos (half_pos hr) hn), div_mul_cancel₀ _ hn.ne']
    linarith
  have hh := hhull (hball hz)
  change inner ℝ z y ≤ A + M at hh
  have hinner : inner ℝ z y = (r / 2) * ‖y‖ := by
    dsimp [z]
    rw [inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [starRingEnd_apply, star_trivial]
    field_simp
  rw [hinner] at hh
  linarith
