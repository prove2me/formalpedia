-- Prove2me | solution 1 for AvramDividend.Classical.nonnegative_of_positive_axis_antitone_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T09:35:45.695011+00:00
-- url     : https://prove2.me/submissions/44d01b97-44e6-4d68-af7c-6dd4bec85fb0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open AvramDividend.Classical Set Filter
open scoped Topology

theorem solution
    (g : ℝ → ℝ)
    (hanti : AntitoneOn g (Ioi (0 : ℝ)))
    (hlim : Tendsto g atTop (𝓝 (0 : ℝ))) :
    ∀ x : ℝ, 0 < x → 0 ≤ g x := by
  intro x hx
  have hbound : ∀ᶠ y : ℝ in atTop, g y ≤ g x := by
    filter_upwards [eventually_ge_atTop x] with y hy
    exact hanti hx (lt_of_lt_of_le hx hy) hy
  exact le_of_tendsto hlim hbound
