-- Prove2me | solution 2 for ComplementFreeCA.XOSGreedy.greedy_two_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:24:26.660994+00:00
-- url     : https://prove2.me/submissions/05e62e61-abd8-46d8-88ba-ef156ba4f0a4

import Mathlib
import Definitions.Def_ComplementFreeCA_XOSGreedy_Model
import Definitions.Def_ComplementFreeCA_XOSGreedy_GreedyRun
import Theorems.Thm_ComplementFreeCA_XOSGreedy_optimal_welfare_le_two_final_prices
import Theorems.Thm_ComplementFreeCA_XOSGreedy_final_prices_le_welfare

-- carved verbatim out of submission 90dc965d-0a9c-4e05-8012-1030f337c085, lines 226-234

section
open Finset ComplementFreeCA.XOSGreedy

theorem solution {n m : ℕ} (E : Fin n → XOSExpr m)
    (dem : Fin n → (Fin m → ℝ) → Finset (Fin m)) (cl : Fin n → Finset (Fin m) → (Fin m → ℝ))
    (hdem : IsDemandOracle E dem) (hcl : IsXOSOracle E cl)
    (O : Fin n → Finset (Fin m)) (hO : IsAllocation O) :
    welfare E O ≤ 2 * welfare E (greedyAlloc dem cl) := by
  have h1 := ComplementFreeCA.XOSGreedy.optimal_welfare_le_two_final_prices E dem cl hdem hcl O hO
  have h2 := ComplementFreeCA.XOSGreedy.final_prices_le_welfare E dem cl hdem hcl
  linarith

end
