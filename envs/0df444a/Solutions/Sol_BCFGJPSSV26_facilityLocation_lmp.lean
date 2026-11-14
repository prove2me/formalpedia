-- Prove2me | solution 1 for BCFGJPSSV26.facilityLocation_lmp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:17:32.6002+00:00
-- url     : https://prove2.me/submissions/087a012e-d5d5-4d25-8e69-456f50caba85

module

public import Definitions.Def_BCFGJPSSV26_Model
import Definitions.Def_BCFGJPSSV26_Combine
public import Definitions.Def_BCFGJPSSV26_Greedy_PolyTime_Main
public import Definitions.Def_BCFGJPSSV26_Combine
public import Definitions.Def_BCFGJPSSV26_Stable_Time_RunTime
import Definitions.Def_BCFGJPSSV26_FL_Main
public import Theorems.Thm_BCFGJPSSV26_FL_fl_main

set_option maxSynthPendingDepth 3



public section

namespace BCFGJPSSV26

open Encoding

/-- **Theorem 1.4** of [BCFGJPSSV26a] (Theorem 4.3 in full): a polynomial-time `1.9499`-LMP
approximation algorithm for uncapacitated facility location. Given an instance with at least one
client and an opening cost `f ≥ 0`, it outputs a nonempty set `S` of distinct facilities with
`cost S ≤ 1.9499 (OPT_f - f |S|)`. -/
theorem facilityLocation_lmp :
    ∃ A : Instance × ℚ → List ℕ,
      Turing.MultiTapeTM.ComputableInPolyTime A (encPair encInstance encRat) encCenters ∧
      ∀ I : Instance, I.Valid → 0 < I.n → ∀ f : ℚ, 0 ≤ f →
        I.IsCenterList (A (I, f)) ∧
        I.cost (I.centers (A (I, f))) ≤
          1.9499 * (I.optFL (f : ℝ) - (f : ℝ) * (A (I, f)).length) :=
  FL.fl_main

end BCFGJPSSV26

end

public section

theorem solution : type_of% @BCFGJPSSV26.facilityLocation_lmp := @BCFGJPSSV26.facilityLocation_lmp
