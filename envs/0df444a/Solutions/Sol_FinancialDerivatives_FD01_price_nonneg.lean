-- Prove2me | solution 1 for FinancialDerivatives.FD01.price_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:07:08.230642+00:00
-- url     : https://prove2.me/submissions/b4ca2d2b-a660-452f-9e55-b77e001b7e5d

import Mathlib


import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price

open Finset

open FinancialDerivatives.FD01 in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f : Ω → ℝ) (h : ∀ ω, 0 ≤ f ω) :
  0 ≤ m.price f := sum_nonneg fun ω _ => mul_nonneg (m.statePrice_nonneg ω) (h ω)
