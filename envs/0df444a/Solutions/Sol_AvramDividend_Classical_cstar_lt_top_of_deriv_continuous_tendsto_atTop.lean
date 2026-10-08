-- Prove2me | solution 1 for AvramDividend.Classical.cstar_lt_top_of_deriv_continuous_tendsto_atTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T14:12:09.275976+00:00
-- url     : https://prove2.me/submissions/eeea843c-f6cb-447b-8810-acecc8571a0d

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open Filter Set Topology
open scoped ENNReal
open AvramDividend.Classical

-- Conditional analytic bridge, not the canonical mission theorem.
-- Uncompiled; no Open platform theorem is imported.
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
    obtain ⟨d, hd, hsmall⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
    obtain ⟨R, hlarge⟩ := eventually_atTop.mp
      (htop.eventually (eventually_ge_atTop (f x₀)))
    let l : ℝ := min (d / 2) x₀
    let u : ℝ := max R x₀
    have hdpos : 0 < d := hd
    have hl : 0 < l := lt_min (by linarith only [hdpos]) hx₀
    have hld : l < d := lt_of_le_of_lt (min_le_left _ _) (by linarith only [hdpos])
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
    (htop : Tendsto (deriv W) atTop atTop) : cstar W < ⊤ := by
  classical
  by_cases hne : (cstarSet W).Nonempty
  · rw [cstar, if_pos hne]
    obtain ⟨a, ha⟩ := hne
    exact (iInf_le_of_le a (iInf_le_of_le ha le_rfl)).trans_lt
      ENNReal.ofReal_lt_top
  · have hzero : ∀ x : ℝ, 0 < x →
        derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by
      rcases positive_minimum_or_boundary (deriv W) hcont htop with hmin | hz
      · obtain ⟨a, ha, hamin⟩ := hmin
        exact (hne ⟨a, ha, hamin⟩).elim
      · simpa only [derivZeroPlus] using hz
    rw [cstar, if_neg hne, if_pos hzero]
    exact ENNReal.zero_lt_top
