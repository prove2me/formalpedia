-- Prove2me | solution 1 for CongestionPoA.AsymSum.pure_poa_sum_eq_five_halves
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T17:44:53.086499+00:00
-- url     : https://prove2.me/submissions/02b951df-f3e9-4070-bea8-38668ca69269

import Theorems.Thm_CongestionPoA_AsymSum_theorem1_sum_le_five_halves
import Theorems.Thm_CongestionPoA_AsymSum_theorem2_instance

set_option autoImplicit false

open CongestionPoA.AsymSum

theorem solution :
    (∀ {ι E : Type} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]
        (G : CongestionGame ι E) (A P : ι → Finset E),
        IsLinear G → IsPureNash G A → IsProfile G P → sumCost G A ≤ 5 / 2 * sumCost G P) ∧
    (∀ N : ℕ, 3 ≤ N →
      ∃ (E : Type) (_ : Fintype E) (_ : DecidableEq E) (G : CongestionGame (Fin N) E)
        (A P : Fin N → Finset E),
        IsLinear G ∧ IsPureNash G A ∧ IsProfile G P ∧
          (∀ Q : Fin N → Finset E, IsProfile G Q → sumCost G P ≤ sumCost G Q) ∧
          0 < sumCost G P ∧ sumCost G A = 5 / 2 * sumCost G P) := by
  constructor
  · intro ι E _ _ _ _ G A P hlin hA hP
    exact theorem1_sum_le_five_halves G A P hlin hA hP
  · intro N hN
    exact theorem2_instance N hN
