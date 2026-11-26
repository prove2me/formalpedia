-- Prove2me | solution 1 for Eden.torus_no_positive_return
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:39.364646+00:00
-- url     : https://prove2.me/submissions/dbfab825-d473-4dec-a07b-b98527d71250

import Definitions.Def_Eden_RadialReturns
import Mathlib.NumberTheory.Real.Irrational
import Definitions.Def_Eden_RotationReturns
import Theorems.Thm_Eden_one_radius_zero_of_evolution_return

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {p : PhaseSpace} (hp : p ∈ torus)
    {t : ℝ} (ht : 0 < t) : evolution c t p ≠ p := by
  intro h
  rcases one_radius_zero_of_evolution_return c ht h with h₁ | h₂
  · linarith [hp.1]
  · linarith [hp.2.1]
end Eden
