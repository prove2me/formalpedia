-- Prove2me | solution 1 for BCFGJPSSV26.FL.sol_eta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:52:50.405809+00:00
-- url     : https://prove2.me/submissions/051c868f-5da0-462f-aebb-9279d6b42630

module

public import Definitions.Def_BCFGJPSSV26_FL_Select
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Core
public import Definitions.Def_BCFGJPSSV26_FL_Run
import all Definitions.Def_BCFGJPSSV26_FL_Run

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.FL

open Finset Greedy

variable {I : Instance}

/-- Solutions do not depend on the slack parameter `η` of the parameters (only on the slack
argument). -/
theorem sol_eta {n m : ℕ} {P : Par} {d : Fin n → Fin m → ℚ} {f η : ℚ}
    {H : List (List (Atom m))} (h : Sol P d f η H) (η' : ℚ) : Sol { P with η := η' } d f η H :=
  h

end BCFGJPSSV26.FL

end

public section

theorem solution : type_of% @BCFGJPSSV26.FL.sol_eta := @BCFGJPSSV26.FL.sol_eta
