-- Prove2me | solution 1 for BCFGJPSSV26.kMedian_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:35:42.170834+00:00
-- url     : https://prove2.me/submissions/f4c121f2-f529-49ac-b06f-037d2e6deb73

module

public import Definitions.Def_BCFGJPSSV26_Model
import Definitions.Def_BCFGJPSSV26_Combine
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Main
public import Definitions.Def_BCFGJPSSV26_Combine
public import Definitions.Def_BCFGJPSSV26_Stable_Time_RunTime
import Definitions.Def_BCFGJPSSV26_FL_Main
public import Theorems.Thm_BCFGJPSSV26_Combine_thm11_of
public import Theorems.Thm_BCFGJPSSV26_kMedian_pseudoApproximation
public import Theorems.Thm_BCFGJPSSV26_stable_kMedian_approximation

set_option maxSynthPendingDepth 3



public section

namespace BCFGJPSSV26

open Encoding

/-- **Theorem 1.1** of [BCFGJPSSV26a]: a randomized polynomial-time `1.95`-approximation algorithm
for k-median. It always outputs at most `k` distinct facilities, and with probability at least
`2/3` their cost is at most `1.95` times the optimum. -/
theorem kMedian_approximation :
    ∃ (A : Instance × List Bool → List ℕ) (e : ℕ),
      RunsInTime encInstance encCenters A (fun I ↦ ((encInstance I).length + 2) ^ e) ∧
      ∀ I : Instance, I.Valid →
        (∀ r, I.IsCenterList (A (I, r)) ∧ (A (I, r)).length ≤ I.k) ∧
        2 / 3 ≤ coinProb (((encInstance I).length + 2) ^ e)
          fun r ↦ I.cost (I.centers (A (I, r))) ≤ 1.95 * I.opt I.k :=
  Combine.thm11_of kMedian_pseudoApproximation stable_kMedian_approximation

end BCFGJPSSV26

end

public section

theorem solution : type_of% @BCFGJPSSV26.kMedian_approximation := @BCFGJPSSV26.kMedian_approximation
