-- Prove2me | solution 1 for Eden.secondCircle_ne_secondCircle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:15:01.958521+00:00
-- url     : https://prove2.me/submissions/35d47073-a9bb-4c05-b305-f8b339d4a2dd

import Definitions.Def_Eden_CircleOrbits
import Mathlib.Data.Set.Card
import Definitions.Def_Eden_PeriodicOrbits
import Theorems.Thm_Eden_secondCircle_nonempty

set_option autoImplicit true
noncomputable section
open Set
open Eden
namespace Eden
theorem _root_.solution {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≠ u) :
    secondCircle s ≠ secondCircle u := by
  intro heq
  obtain ⟨p, hp⟩ := secondCircle_nonempty hs
  have hq : p ∈ secondCircle u := heq ▸ hp
  exact hsu (hp.2.1.symm.trans hq.2.1)
end Eden
