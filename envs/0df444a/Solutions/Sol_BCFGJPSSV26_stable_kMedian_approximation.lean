-- Prove2me | solution 1 for BCFGJPSSV26.stable_kMedian_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:32:30.044991+00:00
-- url     : https://prove2.me/submissions/eff1d4ad-d0a5-49bc-8966-0e126d8e9b40

module

public import Definitions.Def_BCFGJPSSV26_Model
import Definitions.Def_BCFGJPSSV26_Combine
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Main
public import Definitions.Def_BCFGJPSSV26_Combine
public import Definitions.Def_BCFGJPSSV26_Stable_Time_RunTime
import Definitions.Def_BCFGJPSSV26_FL_Main
public import Theorems.Thm_BCFGJPSSV26_Stable_stable_main

set_option maxSynthPendingDepth 3



public section

namespace BCFGJPSSV26

open Encoding

/-- **Theorem 1.3** of [BCFGJPSSV26a], **Theorem 1.1** of [BCFGJPSSV26b]: an algorithm that,
given an instance, a number `L` and a rational accuracy `ε`, runs in time
`O(2^(e L) (N + 2)^e + N + L + |ε|)` with `e = a (⌈1/ε⌉ + 1)^b`, where `N` is the encoded length
of the instance and `|ε|` that of `ε` (not its absolute value), always outputs exactly `k`
distinct facilities, and, if `ε ∈ (0, 1/200)` and the instance is `β`-stable with `L ≥ 1/β`, with
probability at least `1 - ε` outputs facilities of cost at most `(1.89 + C ε)` times the
optimum. -/
theorem stable_kMedian_approximation :
    ∃ (A : ((Instance × ℕ) × ℚ) × List Bool → List ℕ) (a b : ℕ) (C : ℝ),
      RunsInTime (encPair (encPair encInstance encUnary) encRat) encCenters A
        (stableTimeOf a b) ∧
      ∀ I : Instance, I.Valid → I.k ≤ I.m → ∀ (L : ℕ) (ε : ℚ),
        (∀ r, I.IsCenterList (A (((I, L), ε), r)) ∧ (A (((I, L), ε), r)).length = I.k) ∧
        (0 < ε → ε < 1 / 200 → ∀ β : ℝ, 0 < β → I.IsStable β → 1 / β ≤ L →
          1 - (ε : ℝ) ≤ coinProb (stableTimeOf a b ((I, L), ε))
            fun r ↦ I.cost (I.centers (A (((I, L), ε), r))) ≤
              (1.89 + C * ε) * I.opt I.k) :=
  Stable.stable_main

end BCFGJPSSV26

end

public section

theorem solution : type_of% @BCFGJPSSV26.stable_kMedian_approximation := @BCFGJPSSV26.stable_kMedian_approximation
