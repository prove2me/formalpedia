-- Prove2me | solution 1 for Eden.planarAmplitude_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:18.056819+00:00
-- url     : https://prove2.me/submissions/63cf4465-4698-43b5-a91b-b2ddc7ec2446

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
    0 < planarAmplitude t s :=
  Real.sqrt_pos.2 (amplitudeSq_pos ht hs)
end Eden
