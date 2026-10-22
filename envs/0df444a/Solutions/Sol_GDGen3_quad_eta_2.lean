-- Prove2me | solution 2 for GDGen3.quad_eta
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-12T05:46:39.793623+00:00
-- url     : https://prove2.me/submissions/03b889a4-812e-4c07-b071-2e4d2197e51d

import Mathlib
import Definitions.Def_GDGen3Base

noncomputable section

open Finset

open GDGen3

theorem solution (r : ℝ) (N : ℕ) (ξ : ℕ → ℝ)
    (hquad : ∀ i : ℕ, i < N → pj r (i + 1) * ξ i * (1 + ξ i + C r N i) = X r N i) (i : ℕ) (hi : i < N) :
    pj r (i + 1) * ξ i * (1 + eta r N ξ i) = X r N i := by
  simpa only [eta, add_assoc] using hquad i hi
