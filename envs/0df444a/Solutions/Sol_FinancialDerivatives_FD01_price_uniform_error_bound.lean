-- Prove2me | solution 1 for FinancialDerivatives.FD01.price_uniform_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:07:05.823615+00:00
-- url     : https://prove2.me/submissions/bfa3dacc-50d6-4e4a-bf3b-7ce524828e67

import Mathlib


import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price

open Finset

open FinancialDerivatives.FD01 in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f g : Ω → ℝ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ ω, |f ω - g ω| ≤ B) :
  |m.price f - m.price g| ≤ m.discount * B := by
  unfold FinitePriceSystem.price
  rw [← sum_sub_distrib, ← m.statePrice_sum, sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ω _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg (m.statePrice_nonneg ω)]
  exact mul_le_mul_of_nonneg_left (h ω) (m.statePrice_nonneg ω)
