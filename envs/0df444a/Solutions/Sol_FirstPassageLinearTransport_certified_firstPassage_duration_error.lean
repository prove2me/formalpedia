-- Prove2me | solution 1 for FirstPassageLinearTransport.certified_firstPassage_duration_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:39:26.733844+00:00
-- url     : https://prove2.me/submissions/12e9a2d6-ed7c-4f81-bc5d-11f3e1000fa1

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Theorems.Thm_FirstPassageLinearTransport_certified_firstPassage_duration_corridor


set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {x m q h : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hxShell : x ∈ dyadicShell m)
    (hxGood : x ∈ initialWindowGood t)
    (hhm : h ≤ m) (hh : 0 < h)
    (hfp : IsFirstPassage (2 ^ q) x h) :
    |driftGap * (h : ℝ) - ((m : ℝ) - (q : ℝ))| ≤
      t * (m : ℝ) + t + 2 := by
  have hc := certified_firstPassage_duration_corridor ht0 ht1 hxShell
    hxGood hhm hh hfp
  rw [abs_le]
  constructor <;> nlinarith
end FirstPassageLinearTransport
