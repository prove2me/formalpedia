-- Prove2me | solution 1 for DualSepClusterLP.approximateSeparation
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-19T14:48:37.723979+00:00
-- url     : https://prove2.me/submissions/4cdc5743-1ffc-452e-bbfb-33cf2e089a41

import Theorems.Thm_DualSepClusterLP_separatorLocalFeasibility
import Theorems.Thm_DualSepClusterLP_separatorLocalSearch

open DualSepClusterLP

theorem solution :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (A a b : ℕ),
      (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ (t n : ℕ) (G : Graph n) (q : Fin n → ℚ),
        ∃ result : Option (Finset (Fin n)),
          Nonempty (Turing.TM2OutputsInTime M.tm
            ((separationInput t G q).map M.inputAlphabet.symm)
            (some ((separationOutput result).map M.outputAlphabet.symm))
            (2 ^ (A * (t+1)^a) * (n+(pricesBits q).length+1)^b)) ∧
          match result with
          | some S => subsetCost G S < ∑ i ∈ S, (q i : ℝ)
          | none => DualFeasible G (fun i => (q i : ℝ) / (1 + 1 / ((t : ℝ) + 1))) := by
  obtain ⟨M,A,a,b,hfin,h⟩ := separatorLocalSearch
  refine ⟨M,A,a,b,hfin,?_⟩
  intro t n G q
  obtain ⟨result,hm,hs⟩ := h t n G q
  refine ⟨result,hm,?_⟩
  cases result with
  | some s => exact hs
  | none => exact separatorLocalFeasibility t G q hs
