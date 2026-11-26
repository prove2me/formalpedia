-- Prove2me | solution 1 for Eden.isCompact_torus
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:13:25.597852+00:00
-- url     : https://prove2.me/submissions/c478ec13-11e0-4ef4-9b84-344c6296ab66

import Definitions.Def_Eden_RadialDynamics
import Definitions.Def_Eden_Evolution
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Definitions.Def_Eden_InvariantSets
import Theorems.Thm_Eden_torus_subset_attractor
import Theorems.Thm_Eden_isClosed_torus
import Theorems.Thm_Eden_isCompact_attractor

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution : IsCompact torus :=
  isCompact_attractor.of_isClosed_subset isClosed_torus torus_subset_attractor
end Eden
