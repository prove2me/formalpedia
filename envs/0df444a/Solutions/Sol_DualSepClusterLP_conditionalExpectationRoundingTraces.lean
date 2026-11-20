-- Prove2me | solution 1 for DualSepClusterLP.conditionalExpectationRoundingTraces
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-19T13:32:21.034058+00:00
-- url     : https://prove2.me/submissions/f0a62a58-84d3-4485-8eb9-f9058ac3f6d1

import Theorems.Thm_DualSepClusterLP_sparseRounderTraceCorrect
import Theorems.Thm_DualSepClusterLP_sparseRounderPolynomialTime

open DualSepClusterLP

theorem solution :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (A b : ℕ),
      (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ (n : ℕ) (G : Graph n) (L : SparseWeights n), ValidSupport L →
        let z := fun S => (weightAt L S : ℝ)
        ClockStepOK G z → PivotStepOK G z →
        ∃ C P : Clustering n,
          RoundTraceOK G C z clusterEdgeBudget ∧ RoundTraceOK G P z pivotEdgeBudget ∧
          Nonempty (Turing.TM2OutputsInTime M.tm
            ((roundingInput G L).map M.inputAlphabet.symm)
            (some ((partitionOutput
              (if disagreements G C ≤ disagreements G P then C else P)).map M.outputAlphabet.symm))
            (A * ((roundingInput G L).length + 1)^b)) := by
  obtain ⟨M,A,b,hfin,hm⟩ := sparseRounderPolynomialTime
  refine ⟨M,A,b,hfin,?_⟩
  intro n G L hL z hc hp
  obtain ⟨C,P,hC,hP,he⟩ := sparseRounderTraceCorrect G L hL hc hp
  refine ⟨C,P,hC,hP,?_⟩
  simpa only [he] using hm (roundingInput G L)
