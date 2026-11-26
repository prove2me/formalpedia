-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutCertified_duration_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:09:06.101461+00:00
-- url     : https://prove2.me/submissions/0bdbf24b-6a03-46e5-97ff-e8b0674d2e6a

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Theorems.Thm_FirstPassageLinearTransport_certified_firstPassage_duration_error


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
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
      t * (m : ℝ) + t + 2 :=
  certified_firstPassage_duration_error ht0 ht1 hxShell hxGood hhm hh hfp
end FirstPassageLinearTransport
