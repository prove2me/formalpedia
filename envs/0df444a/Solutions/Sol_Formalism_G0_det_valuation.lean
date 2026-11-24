-- Prove2me | solution 1 for Formalism.G0.det_valuation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:25.769708+00:00
-- url     : https://prove2.me/submissions/ecd8cdac-7127-4935-a9fd-38f9ec7bea14

import Definitions.Def_Formalism_SubspaceCounting_StatementW
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetVal
import Theorems.Thm_Formalism_G0_DetValP_sum_cov_zero
import Theorems.Thm_Formalism_G0_DetValP_part1a
import Theorems.Thm_Formalism_G0_DetValP_part1b
import Theorems.Thm_Formalism_G0_DetValP_part2

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.G0.DetValP
namespace Formalism.G0
theorem _root_.solution : Formalism.G0.DetVal := by
  intro K ι _ _ _ r vec S' A hr hA hv
  simp only
  have hsum := sum_cov_zero vec S' A hv
  refine ⟨fun hS => ⟨?_, ?_⟩, fun hS => ?_⟩
  · intro L _ _ g
    rw [hsum]
    simpa using part1a (K := K) hr vec S' A hv hS g
  · intro hval
    have := hval K (1 : GL (Fin r) K)
    rw [hsum] at this
    exact part1b hr vec S' A hA hv hS this
  · intro hval
    have := hval K (1 : GL (Fin r) K)
    rw [hsum] at this
    exact part2 hr vec S' A hA hv hS this
end Formalism.G0
