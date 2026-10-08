-- Prove2me | solution 2 for ConnesRZ.weil_positivity_implies_RH
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-07T00:22:54.427437+00:00
-- url     : https://prove2.me/submissions/0f46c0d8-ecbd-440f-95ab-8f7e3e2f22c3

import Theorems.Thm_ConnesRZ_quartet_coefficient_energy_separation

open Complex ConnesRZ

theorem solution
    (hpos : ∀ g : ℝ → ℂ, IsTest g → 0 ≤ (weilDistribution (conv g (starInv g))).re) :
    ∀ s : ℂ, IsCriticalZero s → s.re = 1 / 2 := by
  intro s hs
  by_contra hoff
  obtain ⟨g, hg, _, _, _, _, hneg⟩ :=
    ConnesRZ.quartet_coefficient_energy_separation s hs hoff
  have hp := hpos g hg
  linarith
