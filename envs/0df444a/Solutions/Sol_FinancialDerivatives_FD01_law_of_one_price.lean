-- Prove2me | solution 1 for FinancialDerivatives.FD01.law_of_one_price
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:07:03.878848+00:00
-- url     : https://prove2.me/submissions/567ab746-9c2a-43a8-821d-ed02fcd60643

import Mathlib


import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price

open Finset

open FinancialDerivatives.FD01 in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f g : Ω → ℝ) (h : ∀ ω, f ω = g ω) :
  m.price f = m.price g := by rw [funext h]
