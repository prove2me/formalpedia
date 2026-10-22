-- Prove2me | solution 1 for GDGen3.quad_eta
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T05:45:23.606818+00:00
-- url     : https://prove2.me/submissions/dc343072-09af-493a-a718-8d6b01e56773

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (N : ℕ) (ξ : ℕ → ℝ)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + ξ i + C r N i) = X r N i) (i : ℕ) (hi : i < N) :
    pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i := by
  simpa only [eta, add_assoc] using hquad i hi
