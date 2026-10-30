-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_ennreal_sandwich_vanishing_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T20:17:07.794078+00:00
-- url     : https://prove2.me/submissions/5f036547-b5bd-4c0d-8f06-89df4d9bf9e9

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Algebra.Order.Sub.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter
open scoped ENNReal Topology

/-- Genuine Qp killed-branch CDF convergence from a finite limit and
the already proved vanishing exponential no-record error. -/
theorem solution
    {ι : Type*} {l : Filter ι} (f g e : ι → ℝ≥0∞)
    (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hfg : f ≤ᶠ[l] g)
    (hge : g ≤ᶠ[l] (fun i => f i + e i))
    (hg : Tendsto g l (𝓝 L))
    (he : Tendsto e l (𝓝 (0 : ℝ≥0∞))) :
    Tendsto f l (𝓝 L) := by
  have hlow : (fun i => g i - e i) ≤ᶠ[l] f := by
    filter_upwards [hge] with i hi
    exact (tsub_le_iff_right).2 (by simpa only [add_comm] using hi)
  have hsub : Tendsto (fun i => g i - e i) l (𝓝 (L - 0)) :=
    ENNReal.Tendsto.sub hg he (Or.inl hL)
  simp only [tsub_zero] at hsub
  exact Filter.Tendsto.squeeze' hsub hg hlow hfg
