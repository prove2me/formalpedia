-- Prove2me | solution 1 for AvramDividend.Classical.continuous_pos_infimum_dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T21:15:53.902267+00:00
-- url     : https://prove2.me/submissions/c468ccad-677e-44c3-b38e-75f3a4efd29c

import Mathlib

open Filter Set Topology
open scoped ENNReal

theorem solution (f : ℝ → ℝ)
    (hcont : ContinuousOn f (Ioi 0))
    (htop : Filter.Tendsto f Filter.atTop Filter.atTop) :
    (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → f a ≤ f x) ∨
      ∀ x : ℝ, 0 < x →
        Filter.liminf (fun y => ((f y : ℝ) : EReal)) (𝓝[>] (0 : ℝ)) ≤
          ((f x : ℝ) : EReal) := by
  classical
  let u : ℝ → EReal := fun y => ((f y : ℝ) : EReal)
  let L : EReal := Filter.liminf u (𝓝[>] (0 : ℝ))
  by_cases hr : ∀ x : ℝ, 0 < x → L ≤ u x
  · right
    simpa [L, u] using hr
  · left
    push_neg at hr
    obtain ⟨x₀, hx₀, hbelow⟩ := hr
    have hnearE : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), u x₀ < u y := by
      exact Filter.eventually_lt_of_lt_liminf hbelow (by isBoundedDefault)
    have hnear : ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), f x₀ < f y := by
      filter_upwards [hnearE] with y hy
      exact EReal.coe_lt_coe_iff.mp (by simpa [u] using hy)
    rcases (mem_nhdsGT_iff_exists_Ioo_subset.mp hnear) with ⟨δ, hδ, hnearδ⟩
    let d : ℝ := min δ (x₀ / 2)
    have hd : 0 < d := lt_min hδ (half_pos hx₀)
    have hdx₀ : d < x₀ :=
      lt_of_le_of_lt (min_le_right _ _) (half_lt_self hx₀)
    have hsmall : ∀ y : ℝ, 0 < y → y < d → f x₀ < f y := by
      intro y hy0 hyd
      exact hnearδ ⟨hy0, lt_of_lt_of_le hyd (min_le_left _ _)⟩
    have hfarEv : ∀ᶠ y : ℝ in atTop, f x₀ ≤ f y :=
      htop.eventually (eventually_ge_atTop (f x₀))
    rcases eventually_atTop.mp hfarEv with ⟨M₀, hM₀⟩
    let M : ℝ := max M₀ x₀
    have hxM : x₀ ≤ M := le_max_right _ _
    have hfar : ∀ y : ℝ, M ≤ y → f x₀ ≤ f y := by
      intro y hy
      exact hM₀ y ((le_max_left M₀ x₀).trans hy)
    have hdM : d ≤ M := (hdx₀.trans_le hxM).le
    have hcontI : ContinuousOn f (Icc d M) :=
      hcont.mono (fun y hy => hd.trans_le hy.1)
    obtain ⟨a, haI, hamin⟩ :=
      isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hdM) hcontI
    have hxI : x₀ ∈ Icc d M := ⟨hdx₀.le, hxM⟩
    have hax : f a ≤ f x₀ := hamin hxI
    refine ⟨a, hd.trans_le haI.1, ?_⟩
    intro x hx
    rcases lt_or_ge x d with hxd | hdx
    · exact (hax.trans_lt (hsmall x hx hxd)).le
    rcases le_total x M with hxM' | hMx
    · exact hamin ⟨hdx, hxM'⟩
    · exact hax.trans (hfar x hMx)
