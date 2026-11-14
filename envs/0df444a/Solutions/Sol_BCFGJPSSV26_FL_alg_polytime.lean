-- Prove2me | solution 1 for BCFGJPSSV26.FL.alg_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:52:49.211465+00:00
-- url     : https://prove2.me/submissions/5b98d956-f0e8-464f-8997-fe45bffcc745

module

public import Definitions.Def_BCFGJPSSV26_FL_Algorithm
public import Definitions.Def_BCFGJPSSV26_FL_PolyTimeCtx
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxMain
public import Definitions.Def_BCFGJPSSV26_Combine_PolyTime
public import Definitions.Def_BCFGJPSSV26_FL_PolyTime
import all Definitions.Def_BCFGJPSSV26_FL_PolyTime

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.FL

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)
open Greedy Greedy.PT

namespace PT

end PT

/-- **The algorithm of Theorem 1.4 runs in polynomial time.** -/
theorem alg_polytime : ComputableInPolyTime (fun p : Instance × ℚ ↦ alg (toRaw p.1) p.2)
    (encPair encInstance encRat) encCenters :=
  PT.algU_polytime

end BCFGJPSSV26.FL

end

public section

theorem solution : type_of% @BCFGJPSSV26.FL.alg_polytime := @BCFGJPSSV26.FL.alg_polytime
