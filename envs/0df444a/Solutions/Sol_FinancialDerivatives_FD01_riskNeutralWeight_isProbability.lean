-- Prove2me | solution 1 for FinancialDerivatives.FD01.riskNeutralWeight_isProbability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T15:07:01.19566+00:00
-- url     : https://prove2.me/submissions/5742fb85-1679-4a5d-a333-74e45b8cb852

import Mathlib


import Definitions.Def_fd01_FinitePriceSystem
import Definitions.Def_fd01_riskNeutralWeight

open Finset

open FinancialDerivatives.FD01 in
theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω] (m : FinitePriceSystem Ω) :
  (∀ ω, 0 ≤ m.riskNeutralWeight ω) ∧ (∑ ω, m.riskNeutralWeight ω) = 1 := by
  unfold FinitePriceSystem.riskNeutralWeight
  refine ⟨fun ω => div_nonneg (m.statePrice_nonneg ω) m.discount_pos.le, ?_⟩
  rw [← sum_div, m.statePrice_sum, div_self m.discount_pos.ne']
