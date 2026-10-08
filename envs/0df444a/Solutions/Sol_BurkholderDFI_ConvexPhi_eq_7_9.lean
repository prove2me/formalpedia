-- Prove2me | solution 1 for BurkholderDFI.ConvexPhi.eq_7_9
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T07:01:19.803748+00:00
-- url     : https://prove2.me/submissions/5bbadcce-595e-46b4-b77e-7c0a12516a5e

import Mathlib
import Definitions.Def_BurkholderDFI_SquareFnLp_Martingale

open BurkholderDFI.SquareFnLp

theorem solution (Φ : ENNReal → ENNReal) (c : NNReal) (hΦ : IsPhi Φ c) (x y : ENNReal) :
    Φ (x + y) ≤ Φ (2 * x) + Φ (2 * y) ∧
      Φ (2 * x) + Φ (2 * y) ≤ c * (Φ x + Φ y) := by
  constructor
  · have hxy : x + y ≤ 2 * max x y := by
      rw [two_mul]
      exact add_le_add (le_max_left _ _) (le_max_right _ _)
    have hmono : Φ (x + y) ≤ Φ (2 * max x y) := hΦ.mono hxy
    rcases le_total x y with h | h
    · rw [max_eq_right h] at hmono
      exact le_trans hmono (le_add_left le_rfl)
    · rw [max_eq_left h] at hmono
      exact le_trans hmono (le_add_right le_rfl)
  · calc
      Φ (2 * x) + Φ (2 * y) ≤ c * Φ x + c * Φ y :=
        add_le_add (hΦ.growth x) (hΦ.growth y)
      _ = c * (Φ x + Φ y) := by rw [mul_add]
