-- Prove2me | solution 1 for BCFGJPSSV26.kMedian_pseudoApproximation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:24:12.190706+00:00
-- url     : https://prove2.me/submissions/0fa2abbf-6bc7-4f90-8744-987b39389e84

module

public import Definitions.Def_BCFGJPSSV26_Model
import Definitions.Def_BCFGJPSSV26_Combine
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Main
public import Definitions.Def_BCFGJPSSV26_Combine
public import Definitions.Def_BCFGJPSSV26_Stable_Time_RunTime
import Definitions.Def_BCFGJPSSV26_FL_Main
public import Theorems.Thm_BCFGJPSSV26_Greedy_greedy_main

set_option maxSynthPendingDepth 3



public section

namespace BCFGJPSSV26

open Encoding

/-- **Theorem 1.2** of [BCFGJPSSV26a]: for every `ε > 0`, a polynomial-time algorithm that
outputs at most `k + C log n / ε²` distinct facilities, of cost at most `(1.9499 + ε)` times the
optimum with `k` facilities. -/
theorem kMedian_pseudoApproximation :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ A : Instance → List ℕ, Turing.MultiTapeTM.ComputableInPolyTime A encInstance encCenters ∧
        ∀ I : Instance, I.Valid →
          I.IsCenterList (A I) ∧ ((A I).length : ℝ) ≤ I.k + C * Real.log I.n / ε ^ 2 ∧
          I.cost (I.centers (A I)) ≤ (1.9499 + ε) * I.opt I.k :=
  Greedy.greedy_main

end BCFGJPSSV26

end

public section

theorem solution : type_of% @BCFGJPSSV26.kMedian_pseudoApproximation := @BCFGJPSSV26.kMedian_pseudoApproximation
