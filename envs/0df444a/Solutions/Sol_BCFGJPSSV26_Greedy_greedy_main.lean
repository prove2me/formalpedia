-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.greedy_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:20:40.012705+00:00
-- url     : https://prove2.me/submissions/18c8bab6-353f-4041-a1e7-561b4586f317

module

public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Main
public import Definitions.Def_BCFGJPSSV26_Combine
public import Theorems.Thm_BCFGJPSSV26_Greedy_algFor_polytime
public import Theorems.Thm_BCFGJPSSV26_Greedy_algFor_spec

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

/-- **Theorem 1.2** of [BCFGJPSSV26a]: the statement of
`BCFGJPSSV26.kMedian_pseudoApproximation`. -/
theorem greedy_main : Combine.Thm12 :=
  ⟨Cthm, fun _ hε ↦ ⟨fun I ↦ algFor _ (toRaw I), algFor_polytime _, fun _ hI ↦ algFor_spec hε hI⟩⟩

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.greedy_main := @BCFGJPSSV26.Greedy.greedy_main
