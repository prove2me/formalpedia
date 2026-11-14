-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a211_zerojump_fullcell_generator_cancel_to_combined_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:43:28.180471+00:00
-- url     : https://prove2.me/submissions/996025e1-8daa-4a50-a9ea-cf01f0eb0b31

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section
/-- Exact original zero-jump Gaussian full-cell drift and generator cancellation.
   Keep the combined discount/Taylor source, avoiding positive-part overestimates. -/
theorem solution (E0 E1 u v d h r c σ Δ : ℝ) :
 E1*(v-u) -
   (E0*(d*(r-Δ*c) + h/2*((r-Δ*c)^2-Δ*σ^2)) +
      Δ*E0*(σ^2/2*h+c*d)) =
 E1*(v-u)-E0*(d*r+h/2*(r-Δ*c)^2) := by ring
