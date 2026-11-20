-- Prove2me | solution 1 for DeletionCode.PaperParameters.tendsto_L_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:18:15.270184+00:00
-- url     : https://prove2.me/submissions/e3b2a97f-2e48-4fed-8ebd-a8db0e0fcbe6

import Definitions.Def_DeletionCode_UniqueWordParameters
import Definitions.Def_DeletionCode_HeaderRecovery
import Mathlib.Analysis.Asymptotics.Defs
import Definitions.Def_DeletionCode_PaperParameters
import Theorems.Thm_DeletionCode_PaperParameters_eventually_threshold

set_option autoImplicit true
open DeletionCode DeletionCode.PaperParameters
open Filter Asymptotics
open scoped Topology
namespace DeletionCode.PaperParameters
theorem _root_.solution : Tendsto L atTop atTop :=
  tendsto_atTop.2 eventually_threshold
end DeletionCode.PaperParameters
