-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.algFor_polytime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:59:26.783032+00:00
-- url     : https://prove2.me/submissions/042e1831-3098-4c84-8492-c6c02665c3de

module

public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Core
public import Definitions.Def_BCFGJPSSV26_Greedy_Constants
public import Definitions.Def_BCFGJPSSV26_Combine_PolyTime
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Nat_Log
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_AuxMain
public import Definitions.Def_BCFGJPSSV26_Stable_Time_PolyTimeLS
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Main
import all Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Main
public import Theorems.Thm_BCFGJPSSV26_Greedy_core_polytime

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Turing.MultiTapeTM ComputableInPolyTime
open Encoding (encRat)

theorem coreRuns_polytime (c : Consts) :
    ComputableInPolyTime (coreRuns c) encCoreIn (encList (encList encNat)) :=
  mapWithInput (f := fun x Λ ↦ core c (scaledIn c x Λ)) guessesU_polytime
    ((core_polytime c).comp (scaledIn_polytime c))

theorem algMain_polytime (c : Consts) :
    ComputableInPolyTime (algMain c) encCoreIn (encList encNat) := by
  have hT := trivialSol_polytime.comp rawU_raw_polytime
  have hle : ComputableInPolyTime
      (fun x ↦ decide ((trivialSol x).length ≤ x.k + bcomp c x.n)) encCoreIn encBool :=
    binary_le' (unary_to_binary.comp ((length_list _).comp hT))
      ((bcompBound_polytime c).comp rawU_raw_polytime)
  have hbest := Combine.best_polytime (raw_n_polytime.comp rawU_raw_polytime)
    (raw_m_polytime.comp rawU_raw_polytime) ((kR_polytime c).comp rawU_raw_polytime)
    (raw_table_polytime.comp rawU_raw_polytime) (coreRuns_polytime c)
  exact ite_decide (trivialSol_isNil_polytime.comp rawU_raw_polytime) (const [0])
    (ite_decide hle hT hbest)

/-- **The algorithm for `ε` runs in polynomial time.** -/
theorem algFor_polytime (ε : ℝ) :
    ComputableInPolyTime (fun I ↦ algFor ε (toRaw I)) encInstance encCenters := by
  unfold algFor
  split_ifs
  · exact algLS_polytime.comp toRaw_polytime
  · exact (algMain_polytime _).comp toRawU_polytime

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.algFor_polytime := @BCFGJPSSV26.Greedy.algFor_polytime
