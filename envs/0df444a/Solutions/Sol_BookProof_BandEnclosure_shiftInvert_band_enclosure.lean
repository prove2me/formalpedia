-- Prove2me | solution 1 for BookProof.BandEnclosure.shiftInvert_band_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:37:42.755957+00:00
-- url     : https://prove2.me/submissions/9b251294-2bf0-4a3a-bdd8-703010870ee7

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false

theorem solution {lo hi : ℕ → ℝ} {nu lam gam : ℝ}
    (hlopos : ∀ m, 0 < lo m) (hband : ∀ m, nu ∈ Set.Icc (lo m) (hi m))
    (hmap : lam = nu⁻¹ - gam) :
    ∀ m, lam ∈ Set.Icc ((hi m)⁻¹ - gam) ((lo m)⁻¹ - gam) := by
  intro m
  rcases hband m with ⟨hl, hu⟩
  have hn : 0 < nu := lt_of_lt_of_le (hlopos m) hl
  rw [hmap]
  exact ⟨sub_le_sub_right (inv_anti₀ hn hu) gam,
    sub_le_sub_right (inv_anti₀ (hlopos m) hl) gam⟩

#print axioms solution
