-- Prove2me | solution 1 for Eden.hasDerivAt_planarAmplitude
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:10:39.158887+00:00
-- url     : https://prove2.me/submissions/3cd8ea20-4145-4228-ba69-5ef484aaa1e2

import Definitions.Def_Eden_ScalarFlow
import Mathlib.Tactic.FunProp
import Definitions.Def_Eden_ScalarCalculus
import Theorems.Thm_Eden_hasDerivAt_planarAmplitude_of_pos
import Theorems.Thm_Eden_amplitudeSq_pos
import Theorems.Thm_Eden_radialDiscriminant_pos


set_option autoImplicit true
noncomputable section
open scoped Topology
open Filter
open Eden
namespace Eden
theorem _root_.solution {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    HasDerivAt (fun τ => planarAmplitude τ s)
      (q (squaredRadiusEvolution t s) * planarAmplitude t s) t :=
  hasDerivAt_planarAmplitude_of_pos (radialDiscriminant_pos ht s) (amplitudeSq_pos ht hs)
end Eden
