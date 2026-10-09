-- Prove2me | solution 1 for ConnesRZFrontier.weilPositive_iff_mathlib_RH
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-08T16:49:09.309544+00:00
-- url     : https://prove2.me/submissions/b4cc23b0-c101-45b0-9fdd-6478977a0780

import Theorems.Thm_ConnesRZ_weil_positivity_implies_RH
import Theorems.Thm_ConnesRZ_weil_positivity_of_RH
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Definitions.Def_ConnesRZ_weil_defs
import Mathlib.NumberTheory.LSeries.Nonvanishing
set_option autoImplicit false
open Complex

theorem solution :
    (∀ g : ℝ → ℂ, ConnesRZ.IsTest g →
      0 ≤ (ConnesRZ.weilDistribution (ConnesRZ.conv g (ConnesRZ.starInv g))).re) ↔
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_zeros_in_strip_on_line]
  constructor
  · intro hpos s hz hlower hupper
    exact ConnesRZ.weil_positivity_implies_RH hpos s ⟨hz, hlower, hupper⟩
  · intro hstrip g hg
    apply ConnesRZ.weil_positivity_of_RH ?_ g hg
    intro s hs
    exact hstrip s hs.1 hs.2.1 hs.2.2
