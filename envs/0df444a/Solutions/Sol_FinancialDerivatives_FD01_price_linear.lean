-- Prove2me | solution 1 for FinancialDerivatives.FD01.price_linear
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:07:06.681968+00:00
-- url     : https://prove2.me/submissions/f6bca389-6a17-4c3a-b319-0e4e782e357e

import Mathlib


import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price

open Finset

open FinancialDerivatives.FD01 in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f g : Ω → ℝ) (a b : ℝ) :
  m.price (fun ω => a * f ω + b * g ω) = a * m.price f + b * m.price g := by
  unfold FinitePriceSystem.price; rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun ω _ => by ring
