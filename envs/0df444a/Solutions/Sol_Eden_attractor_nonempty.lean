-- Prove2me | solution 1 for Eden.attractor_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:29:00.789333+00:00
-- url     : https://prove2.me/submissions/438a8fe6-1e9d-47c1-b5bd-bde8bcbae663

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution : attractor.Nonempty := by
  refine ⟨0, ?_⟩
  norm_num [attractor, radiusSq₁, radiusSq₂]
end Eden
