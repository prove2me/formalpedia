-- Prove2me | solution 1 for Eden.planarAmplitude_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:05:40.328509+00:00
-- url     : https://prove2.me/submissions/e3338fa6-dbf3-4d6a-90db-7f801fe73ca5

import Definitions.Def_Eden_ScalarFlow
import Mathlib.Tactic.FunProp
import Definitions.Def_Eden_ScalarCalculus
import Theorems.Thm_Eden_amplitudeSq_pos


set_option autoImplicit true
noncomputable section
open scoped Topology
open Filter
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    planarAmplitude t s ^ 2 = amplitudeSq t s :=
  Real.sq_sqrt (le_of_lt (amplitudeSq_pos ht hs))
end Eden
