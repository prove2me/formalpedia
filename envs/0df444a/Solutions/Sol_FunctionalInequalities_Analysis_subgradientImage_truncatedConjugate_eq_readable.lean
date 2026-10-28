-- Prove2me | solution 1 for FunctionalInequalities.Analysis.subgradientImage_truncatedConjugate_eq_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:00.578984+00:00
-- url     : https://prove2.me/submissions/7867ada4-2e27-4186-a0ed-83d22b1e547d

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Caffarelli
import Theorems.Thm_FunctionalInequalities_Analysis_exists_truncatedConjugate_eq_readable
import Theorems.Thm_FunctionalInequalities_Analysis_n7_subgradient_eq_maximizer_readable

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section LT11F3TruncatedConjugateSubgradients
open scoped RealInnerProductSpace Topology
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.n7_support_min {u : E → ℝ} {x p : E}
    (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) :
    IsMinOn (fun y => u y - ⟪p, y⟫) univ x := by
  intro y _
  have h := hp y
  rw [inner_sub_right] at h
  dsimp
  linarith
private lemma FunctionalInequalities.Analysis.n7_support_unique {u : E → ℝ}
    (hstrict : StrictConvexOn ℝ univ u) {x z p : E}
    (hx : ∀ y, u x + ⟪p, y - x⟫ ≤ u y)
    (hz : ∀ y, u z + ⟪p, y - z⟫ ≤ u y) : x = z := by
  exact (hstrict.sub_concaveOn ((innerₗ E p).concaveOn convex_univ)).eq_of_isMinOn
    (n7_support_min hx) (n7_support_min hz) (mem_univ x) (mem_univ z)
section FiniteDimensional
variable [FiniteDimensional ℝ E]
private lemma FunctionalInequalities.Analysis.n7_support_of_interior_max {u : E → ℝ}
    (hu : Continuous u) (hconv : ConvexOn ℝ univ u) {M : ℝ} (hM : 0 ≤ M)
    {x p : E} (hx : ‖x‖ < M)
    (heq : truncatedConjugate u M p = ⟪p, x⟫ - u x) :
    ∀ y, u x + ⟪p, y - x⟫ ≤ u y := by
  let f : E → ℝ := fun z => u z - ⟪p, z⟫
  have hf : ConvexOn ℝ univ f :=
    hconv.sub ((innerₗ E p).concaveOn convex_univ)
  have hmin : ∀ z ∈ ball (0 : E) M, f x ≤ f z := by
    intro z hz
    have h := (exists_truncatedConjugate_eq_readable hu hM p).2 z
      (closedBall_subset_closedBall (le_refl M)
        (ball_subset_closedBall hz))
    rw [heq] at h
    dsimp [f]
    linarith
  intro y
  have hpre : (AffineMap.lineMap x y) ⁻¹' ball (0 : E) M ∈ 𝓝 (0 : ℝ) :=
    (AffineMap.lineMap_continuous (p := x) (q := y)).continuousAt.preimage_mem_nhds
      (isOpen_ball.mem_nhds (by
        rw [AffineMap.lineMap_apply_zero]
        exact mem_ball_zero_iff.mpr hx))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  let t : ℝ := min (ε / 2) (1 / 2)
  have ht : 0 < t := lt_min (by linarith) (by norm_num)
  have htε : t < ε := (min_le_left _ _).trans_lt (by linarith)
  have ht1 : t < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hz : AffineMap.lineMap x y t ∈ ball (0 : E) M := by
    apply hεsub
    rw [Metric.mem_ball, Real.dist_eq]
    simpa only [sub_zero, abs_of_pos ht] using htε
  have hxz := hmin _ hz
  have hzy := hf.le_right_of_left_le (mem_univ x) (mem_univ y)
    (lineMap_mem_openSegment ℝ x y ⟨ht, ht1⟩) hxz
  have hxy : f x ≤ f y := hxz.trans hzy
  dsimp [f] at hxy
  rw [inner_sub_right]
  linarith
end FiniteDimensional
section FiniteDimensional
variable [FiniteDimensional ℝ E]
/-- **Danskin identification of subgradient images** (weak Letwin route; KLS500
`convexSubgradientImage_truncatedLegendrePotential_eq_relative`): for strictly convex continuous `u`, on a set
`S` of slopes whose ball maximisers lie in the open ball, the subgradient image of the truncated conjugate is the
inverse subgradient image `{x | ∃ p ∈ S, p ∈ ∂u(x)}`. -/
theorem solution {u : E → ℝ} (hu : Continuous u)
    (hstrict : StrictConvexOn ℝ univ u) {M : ℝ} (hM : 0 ≤ M) {S : Set E}
    (hS : ∀ p ∈ S, ∀ x ∈ closedBall (0 : E) M, FunctionalInequalities.Analysis.truncatedConjugate u M p = ⟪p, x⟫ - u x → ‖x‖ < M) :
    FunctionalInequalities.Analysis.subgradientImage (FunctionalInequalities.Analysis.truncatedConjugate u M) S = {x | ∃ p ∈ S, ∀ y, u x + ⟪p, y - x⟫ ≤ u y} := by
  ext g
  constructor
  · rintro ⟨p, hpS, hg⟩
    obtain ⟨x, hxB, heq⟩ := (FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_readable hu hM p).1
    have hx := hS p hpS x hxB heq
    have hp := FunctionalInequalities.Analysis.n7_support_of_interior_max hu hstrict.convexOn hM hx heq
    have hgx := FunctionalInequalities.Analysis.n7_subgradient_eq_maximizer_readable hu hstrict hM hx hp heq hg
    subst g
    exact ⟨p, hpS, hp⟩
  · rintro ⟨p, hpS, hp⟩
    obtain ⟨x, hxB, heq⟩ := (FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_readable hu hM p).1
    have hx := hS p hpS x hxB heq
    have hpx := FunctionalInequalities.Analysis.n7_support_of_interior_max hu hstrict.convexOn hM hx heq
    have hxg : x = g := FunctionalInequalities.Analysis.n7_support_unique hstrict hpx hp
    subst g
    refine ⟨p, hpS, ?_⟩
    intro q
    have hq := (FunctionalInequalities.Analysis.exists_truncatedConjugate_eq_readable hu hM q).2 x hxB
    rw [heq, inner_sub_right]
    have hcomm : ⟪x, q⟫ = ⟪q, x⟫ := real_inner_comm q x
    have hcomm' : ⟪x, p⟫ = ⟪p, x⟫ := real_inner_comm p x
    rw [hcomm, hcomm']
    linarith
