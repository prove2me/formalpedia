-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_unit_inner_le_infDist_frontier_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:30:58.431403+00:00
-- url     : https://prove2.me/submissions/7cc4476f-e815-4953-95d1-f6aebf34c291

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT11C3NearestBoundaryHalfspace
open Set Metric
open scoped RealInnerProductSpace
/-- **Supporting half-space at a nearest boundary point of an open convex set** (weak Letwin route,
Caffarelli's argument, the `dist(x₀, ∂Ω)` factor of the Alexandrov estimate): for a bounded open convex
`Ω` and `x₀ ∈ Ω`, with `d := infDist x₀ (frontier Ω)`, there is a unit vector `e` such that
`⟪x − x₀, e⟫ ≤ d` for every `x ∈ Ω`. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E] {Ω : Set E} (hΩ : IsOpen Ω)
    (hc : Convex ℝ Ω) (hb : Bornology.IsBounded Ω) {x₀ : E} (hx₀ : x₀ ∈ Ω) :
    ∃ e : E, ‖e‖ = 1 ∧ ∀ x ∈ Ω, ⟪x - x₀, e⟫ ≤ infDist x₀ (frontier Ω) := by
  classical
  obtain ⟨r, hr⟩ := hb.subset_closedBall x₀
  have hcompact_ball : IsCompact (closedBall x₀ r) := isCompact_closedBall x₀ r
  have hcompact_frontier : IsCompact (frontier Ω) :=
    hcompact_ball.of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans (closure_minimal hr isClosed_closedBall))
  have hfrontier_nonempty : (frontier Ω).Nonempty := by
    by_contra hne
    have hfrontier_empty : frontier Ω = ∅ := by
      ext y
      constructor
      · intro hy
        exact (hne ⟨y, hy⟩).elim
      · intro hy
        simp at hy
    rw [frontier_eq_empty_iff] at hfrontier_empty
    rcases hfrontier_empty with hΩempty | hΩuniv
    · rw [hΩempty] at hx₀
      exact hx₀
    · obtain ⟨s, hs⟩ := hb.subset_closedBall x₀
      have hs_nonneg : 0 ≤ s := by
        have hsx : dist x₀ x₀ ≤ s := hs hx₀
        simpa only [dist_self] using hsx
      obtain ⟨v, hv⟩ := exists_ne (0 : E)
      have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      have hunit : ‖‖v‖⁻¹ • v‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hvpos)]
        simp [ne_of_gt hvpos]
      let y : E := x₀ + (s + 1) • (‖v‖⁻¹ • v)
      have hyΩ : y ∈ Ω := by
        rw [hΩuniv]
        exact mem_univ y
      have hyball : y ∈ closedBall x₀ s := hs hyΩ
      have hnorm : ‖y - x₀‖ = s + 1 := by
        have hs1 : 0 ≤ s + 1 := by linarith
        calc
          ‖y - x₀‖ = ‖(s + 1) • (‖v‖⁻¹ • v)‖ := by
            dsimp [y]
            rw [add_sub_cancel_left]
          _ = ‖s + 1‖ * ‖‖v‖⁻¹ • v‖ := norm_smul _ _
          _ = (s + 1) * 1 := by
            rw [Real.norm_eq_abs, abs_of_nonneg hs1, hunit]
          _ = s + 1 := by ring
      have hydist : dist y x₀ ≤ s := by
        exact hyball
      rw [dist_eq_norm, hnorm] at hydist
      linarith
  obtain ⟨xb, hxb, hxb_dist⟩ :=
    hcompact_frontier.exists_infDist_eq_dist hfrontier_nonempty x₀
  have hxbΩ : xb ∉ Ω := by
    intro h
    apply hxb.2
    rw [hΩ.interior_eq]
    exact h
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hc hΩ hxbΩ
  let e₀ : E := (InnerProductSpace.toDual ℝ E).symm f
  have hdual (z : E) : inner ℝ e₀ z = f z := by
    dsimp [e₀]
    exact InnerProductSpace.toDual_symm_apply
  have hrepr (z : E) : f z = inner ℝ z e₀ := by
    calc
      f z = inner ℝ e₀ z := (hdual z).symm
      _ = inner ℝ z e₀ := real_inner_comm _ _
  have he₀_ne : e₀ ≠ 0 := by
    intro he₀_zero
    have hzero (z : E) : f z = 0 := by
      rw [hrepr, he₀_zero]
      simp
    have hlt := hf x₀ hx₀
    rw [hzero x₀, hzero xb] at hlt
    exact (lt_irrefl 0) hlt
  let e : E := ‖e₀‖⁻¹ • e₀
  have he_norm : ‖e‖ = 1 := by
    have hnorm_pos : 0 < ‖e₀‖ := norm_pos_iff.mpr he₀_ne
    dsimp [e]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm_pos)]
    simp [ne_of_gt hnorm_pos]
  refine ⟨e, he_norm, ?_⟩
  intro x hx
  have hfx : f x ≤ f xb := (hf x hx).le
  have hgap : f xb - f x₀ ≤ ‖xb - x₀‖ * ‖e₀‖ := by
    calc
      f xb - f x₀ = f (xb - x₀) := (map_sub f xb x₀).symm
      _ = inner ℝ (xb - x₀) e₀ := hrepr (xb - x₀)
      _ ≤ |inner ℝ (xb - x₀) e₀| := le_abs_self _
      _ ≤ ‖xb - x₀‖ * ‖e₀‖ := abs_real_inner_le_norm _ _
  have hrepr_norm (z : E) : inner ℝ z e = f z / ‖e₀‖ := by
    change inner ℝ z (‖e₀‖⁻¹ • e₀) = f z / ‖e₀‖
    rw [real_inner_smul_right, hrepr]
    ring
  have hnorm_pos : 0 < ‖e₀‖ := norm_pos_iff.mpr he₀_ne
  calc
    ⟪x - x₀, e⟫ = (f x - f x₀) / ‖e₀‖ := by
      rw [hrepr_norm, map_sub]
    _ ≤ (f xb - f x₀) / ‖e₀‖ :=
      div_le_div_of_nonneg_right (sub_le_sub_right hfx _) (norm_nonneg _)
    _ ≤ (‖xb - x₀‖ * ‖e₀‖) / ‖e₀‖ :=
      div_le_div_of_nonneg_right hgap (norm_nonneg _)
    _ = ‖xb - x₀‖ := by
      field_simp [ne_of_gt hnorm_pos]
    _ = dist x₀ xb := by
      rw [dist_eq_norm]
      exact norm_sub_rev _ _
    _ = infDist x₀ (frontier Ω) := hxb_dist.symm
