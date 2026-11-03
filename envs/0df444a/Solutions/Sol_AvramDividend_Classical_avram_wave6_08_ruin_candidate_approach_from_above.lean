-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_ruin_candidate_approach_from_above
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T06:58:36.131609+00:00
-- url     : https://prove2.me/submissions/b0727e11-baa0-46bf-af74-4fee08aac288

import Mathlib

open Filter Topology Set

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The candidate may jump at zero from the negative side; the original
ruin source grid only needs an approach from above the terminal reserve. -/
theorem solution
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (hx : x ≤ 0)
    (z : ℕ → ℝ) (hz : ∀ n, x ≤ z n)
    (hlim : Tendsto z atTop (𝓝 x)) :
    Tendsto (fun n => w (z n)) atTop (𝓝 (w x)) := by
  rcases lt_or_eq_of_le hx with hxlt | hxeq
  · have hnhds : Iio (0 : ℝ) ∈ 𝓝 x := isOpen_Iio.mem_nhds hxlt
    have hevent : ∀ᶠ n in atTop, z n < 0 := hlim.eventually hnhds
    have heq : (fun n => w (z n)) =ᶠ[atTop] (fun _ => w x) := by
      filter_upwards [hevent] with n hn
      exact (hw_neg (z n) hn).trans (hw_neg x hxlt).symm
    exact (tendsto_congr' heq).2 tendsto_const_nhds
  · subst x
    have hwithin : Tendsto z atTop (𝓝[Ici (0 : ℝ)] 0) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hlim, Filter.Eventually.of_forall hz⟩
    exact (hw_cont 0 (by simp)).tendsto.comp hwithin
