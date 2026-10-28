-- Prove2me | solution 1 for FinancialDerivatives.FD01.price_mono
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:07:02.160842+00:00
-- url     : https://prove2.me/submissions/fcc183d4-92f0-4c96-b820-e51f22e3496b

import Mathlib


import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price

open Finset

open FinancialDerivatives.FD01 in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f g : Ω → ℝ) (h : ∀ ω, f ω ≤ g ω) :
  m.price f ≤ m.price g := sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (m.statePrice_nonneg ω)
