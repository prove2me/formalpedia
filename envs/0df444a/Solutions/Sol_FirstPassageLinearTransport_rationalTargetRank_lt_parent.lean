-- Prove2me | solution 1 for FirstPassageLinearTransport.rationalTargetRank_lt_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:34:47.77242+00:00
-- url     : https://prove2.me/submissions/ea1fd15a-d952-45bc-a885-0dcc9af9827e

import Definitions.Def_FirstPassageLinearTransport_FirstBadEnvelope
import Definitions.Def_FirstPassageLinearTransport_Pullback
import Definitions.Def_FirstPassageLinearTransport_RecertificationStep

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r : ℚ} (hr0 : 0 ≤ r) (hr1 : r < 1) {m : ℕ} (hm : 0 < m) :
    rationalTargetRank r m < m := by
  have hnonneg : (0 : ℝ) ≤ (r : ℝ) * (m : ℝ) := by positivity
  rw [rationalTargetRank, Nat.floor_lt hnonneg]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hrR : (r : ℝ) < 1 := by exact_mod_cast hr1
  nlinarith
end FirstPassageLinearTransport
