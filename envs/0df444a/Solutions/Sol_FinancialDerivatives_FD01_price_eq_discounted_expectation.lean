-- Prove2me | solution 1 for FinancialDerivatives.FD01.price_eq_discounted_expectation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:07:03.095999+00:00
-- url     : https://prove2.me/submissions/7af1237d-820a-4aed-a625-684e2151e8f9

import Mathlib


import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_price
import Definitions.Def_fd01_riskNeutralWeight

open Finset

open FinancialDerivatives.FD01 in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) (f : Ω → ℝ) :
  m.price f = m.discount * (∑ ω, m.riskNeutralWeight ω * f ω) := by
  unfold FinitePriceSystem.price FinitePriceSystem.riskNeutralWeight
  rw [mul_sum]; refine sum_congr rfl fun ω _ => ?_
  have := m.discount_pos.ne'; field_simp
