-- Prove2me | solution 1 for Eden.torus_subset_attractor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:33.131794+00:00
-- url     : https://prove2.me/submissions/b4ebb705-5b37-43c8-aeb0-6cfc9a6afec2

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution : torus ⊆ attractor := by
  intro p hp
  exact ⟨le_trans hp.1.le (by norm_num), le_trans hp.2.1.le (by norm_num), hp.2.2⟩
end Eden
