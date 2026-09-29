-- Prove2me | solution 1 for ErlerGross.mode_sum_eq_kappa_integral
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T10:10:28.882428+00:00
-- url     : https://prove2.me/submissions/72a59339-8221-4f4a-b67a-15e9c8771301

import Mathlib
import Definitions.Def_ErlerGross_defs
import Theorems.Thm_ErlerGross_kappaIntegrand_integrable
import Theorems.Thm_ErlerGross_mode_sum_eq_B3
import Theorems.Thm_ErlerGross_kappa_integral_eq_residue_sum

open Real Filter Topology MeasureTheory

theorem solution :
    Integrable ErlerGross.kappaIntegrand ∧
      HasSum (fun n : ℕ => 3 * ErlerGross.neumannMEven (n + 1) *
        ErlerGross.betaVec (2 * (n + 1)))
        (2 * ∫ κ, ErlerGross.kappaIntegrand κ) := by
  obtain ⟨_, hmode⟩ := ErlerGross.mode_sum_eq_B3
  have hres := ErlerGross.kappa_integral_eq_residue_sum
  rw [hres.tsum_eq] at hmode
  exact ⟨ErlerGross.kappaIntegrand_integrable, hmode⟩
