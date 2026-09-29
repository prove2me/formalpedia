-- Prove2me | solution 1 for Freiman.lower_other22_reached_target
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T13:04:43.351932+00:00
-- url     : https://prove2.me/submissions/a8a8d784-3a79-4fa6-bbe3-2d3c9a747f60

import Theorems.Thm_Freiman_lower_other22_target
import Definitions.Def_Freiman_lowerOther22
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (t : ℝ) (S : LowerPair) (h : lowerOther22Reached t S) :
    lowerLocalLower S ([2],[1]) ≤ lowerLocalCoordinate S t := by
  rcases h with ⟨Z,B,R,hg,ht,hp⟩
  exact lower_other22_target Z B R S hg t ht hp
