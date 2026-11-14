-- Prove2me | solution 1 for BCFGJPSSV26.FL.fl_main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:14:31.932407+00:00
-- url     : https://prove2.me/submissions/3b5f90d5-07c1-4818-b7a4-cf7cf9f41c4d

module

public import Definitions.Def_BCFGJPSSV26_FL_Run
public import Definitions.Def_BCFGJPSSV26_FL_PolyTime
public import Definitions.Def_BCFGJPSSV26_FL_Main
import all Definitions.Def_BCFGJPSSV26_FL_Main
public import Theorems.Thm_BCFGJPSSV26_FL_alg_polytime
public import Theorems.Thm_BCFGJPSSV26_FL_alg_spec

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.FL

open Encoding

variable {I : Instance}

/-- **Theorem 1.4** of [BCFGJPSSV26a]: the statement of `BCFGJPSSV26.facilityLocation_lmp`. -/
theorem fl_main : Thm14 :=
  ⟨fun p ↦ alg (toRaw p.1) p.2, alg_polytime, fun _ hI hn _ hf ↦ alg_spec hI hn hf⟩

end BCFGJPSSV26.FL

end

public section

theorem solution : type_of% @BCFGJPSSV26.FL.fl_main := @BCFGJPSSV26.FL.fl_main
