-- Prove2me | solution 1 for Eden.firstCircle_ne_firstCircle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:15:00.359895+00:00
-- url     : https://prove2.me/submissions/3ca7dcee-60b0-4c75-b1bb-920682e1ea50

import Definitions.Def_Eden_CircleOrbits
import Mathlib.Data.Set.Card
import Definitions.Def_Eden_PeriodicOrbits
import Theorems.Thm_Eden_firstCircle_nonempty

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≠ u) :
    firstCircle s ≠ firstCircle u := by
  intro heq
  obtain ⟨p, hp⟩ := firstCircle_nonempty hs
  have hq : p ∈ firstCircle u := heq ▸ hp
  exact hsu (hp.1.symm.trans hq.1)
end Eden
