-- Prove2me | solution 1 for Eden.outerRadialRegion_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:08.583964+00:00
-- url     : https://prove2.me/submissions/a802a3cd-d6c4-4611-8c3c-d59b36d835b2

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
import Theorems.Thm_Eden_firstCircle_nonempty


set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution : outerRadialRegion.Nonempty := by
  obtain ⟨p, hp⟩ := firstCircle_nonempty (show (0 : ℝ) ≤ 2 by norm_num)
  refine ⟨p, ⟨?_, ?_⟩⟩
  · exact ⟨hp.1.le, by rw [hp.2.1]; norm_num, hp.2.2⟩
  · rw [hp.1]; norm_num
end Eden
