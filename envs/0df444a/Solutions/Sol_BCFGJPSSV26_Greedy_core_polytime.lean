-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.core_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:56:18.565061+00:00
-- url     : https://prove2.me/submissions/e45bc9a4-f46e-4d82-b7a2-a583df67d82d

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Defs
public import Definitions.Def_BCFGJPSSV26_Basic_Raw
public import Definitions.Def_BuhaiPapers_Background_PolyTime_Rat
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxCore
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Core
import all Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Core

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Turing.MultiTapeTM

/-- **The core runs in polynomial time**, for fixed constants. -/
theorem core_polytime (c : Consts) : ComputableInPolyTime (core c) encCoreIn (encList encNat) :=
  PT.coreS c (X := fun x ↦ x) ComputableInPolyTime.id'

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.core_polytime := @BCFGJPSSV26.Greedy.core_polytime
