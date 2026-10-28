-- Prove2me | solution 1 for D1Bound5.Prove2MeTransfer.pellCoverageLightBlock00_20261024
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T07:30:22.895295+00:00
-- url     : https://prove2.me/submissions/dcf1948e-2a99-49fb-accf-3b1ce24f35d4

import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellFiniteFieldCoverageLight_Definitions

section
namespace D1Bound5
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem _root_.solution : ∀ k : Fin 50, PellFieldCoverageLightAt (0+k.val) := by
  decide +kernel

end D1Bound5
end
