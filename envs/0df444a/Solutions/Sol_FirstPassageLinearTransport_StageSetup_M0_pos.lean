-- Prove2me | solution 1 for FirstPassageLinearTransport.StageSetup.M0_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:32:13.305906+00:00
-- url     : https://prove2.me/submissions/3970c827-a132-4bf7-8e32-ca0d4d04f1d0

import Definitions.Def_FirstPassageLinearTransport_Parameters
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
namespace StageSetup
theorem _root_.solution {r eta : ℝ} (p : StageSetup r eta) :
    1 ≤ p.M0 := by
  by_contra h
  have hzero : p.M0 = 0 := by omega
  have ht := p.target_one_lt p.M0 le_rfl
  rw [hzero] at ht
  norm_num [targetScale] at ht
end StageSetup
end FirstPassageLinearTransport
