-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger79_original_gaussian_cell_discount_taylor_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T08:24:28.594413+00:00
-- url     : https://prove2.me/submissions/b07a2453-a600-4f07-aca2-66d15add1ce4

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- Discount, Gaussian second-order Taylor and centred drift-cell identity. -/
theorem solution
    (E F W Wh a b c z Δ v q : ℝ) :
    ((F - E) * W + F * (Wh - W)) -
      E * (a * z + (b / 2) * (z ^ 2 - Δ * v)) -
      Δ * E * (a * c + (b / 2) * v - q * W) =
    (F - E + q * Δ * E) * W +
      (F - E) * (Wh - W) +
      E * (Wh - W - a * (z + c * Δ) -
        (b / 2) * (z + c * Δ) ^ 2) +
      E * b * (c * Δ * z + c ^ 2 * Δ ^ 2 / 2) := by
  ring
