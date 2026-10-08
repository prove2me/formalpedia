-- Prove2me | solution 1 for AvramDividend.Classical.cstar_finite_of_deriv_continuous_positive_axis_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T16:17:56.266462+00:00
-- url     : https://prove2.me/submissions/92818223-1739-4911-ac09-63a39a28ddb9

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_iff_minimizer_or_zero_boundary

open Filter Set Topology
open scoped ENNReal
open AvramDividend.Classical

private theorem positive_minimum_or_boundary (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Ioi 0))
    (htop : Tendsto f atTop atTop) :
    (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → f a ≤ f x) ∨
      ∀ x : ℝ, 0 < x →
        Filter.liminf (fun y => (f y : EReal)) (𝓝[>] (0 : ℝ)) ≤
          (f x : EReal) := by
  classical
  by_cases hzero : ∀ x : ℝ, 0 < x →
      Filter.liminf (fun y => (f y : EReal)) (𝓝[>] (0 : ℝ)) ≤ (f x : EReal)
  · exact Or.inr hzero
  · push_neg at hzero
    obtain ⟨x₀, hx₀, hgap⟩ := hzero
    have hnear : ∀ᶠ y in 𝓝[>] (0 : ℝ), (f x₀ : EReal) < (f y : EReal) :=
      eventually_lt_of_lt_liminf hgap
    obtain ⟨δ, hδ, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
    have hδpos : 0 < δ := Set.mem_Ioi.mp hδ
    obtain ⟨R, hlarge⟩ := eventually_atTop.mp
      (htop.eventually (eventually_ge_atTop (f x₀)))
    let l : ℝ := min (δ / 2) x₀
    let u : ℝ := max R x₀
    have hl : 0 < l := lt_min (by linarith) hx₀
    have hld : l < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hxI : x₀ ∈ Icc l u := ⟨min_le_right _ _, le_max_right _ _⟩
    obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨x₀, hxI⟩
      (hcont.mono (show Icc l u ⊆ Ioi 0 from
        fun x hx => lt_of_lt_of_le hl hx.1))
    have hax₀ : f a ≤ f x₀ := hmin hxI
    refine Or.inl ⟨a, lt_of_lt_of_le hl ha.1, ?_⟩
    intro x hx
    by_cases hxl : x < l
    · exact hax₀.trans (EReal.coe_lt_coe_iff.mp
        (hsmall ⟨hx, hxl.trans hld⟩)).le
    · by_cases hux : u < x
      · exact hax₀.trans (hlarge x ((le_max_left R x₀).trans hux.le))
      · exact hmin ⟨le_of_not_gt hxl, le_of_not_gt hux⟩

theorem solution (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Ioi 0))
    (htop : Tendsto (deriv W) atTop atTop) :
    cstar W < ⊤ := by
  rcases positive_minimum_or_boundary (deriv W) hcont htop with hmin | hzero
  · obtain ⟨a, ha, hamin⟩ := hmin
    exact (cstar_lt_top_iff_minimizer_or_zero_boundary W).2
      (Or.inl ⟨a, ha, hamin⟩)
  · exact (cstar_lt_top_iff_minimizer_or_zero_boundary W).2
      (Or.inr (by simpa only [derivZeroPlus] using hzero))
