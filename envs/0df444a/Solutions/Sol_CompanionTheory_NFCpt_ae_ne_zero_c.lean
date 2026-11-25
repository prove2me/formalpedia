-- Prove2me | solution 1 for CompanionTheory.NFCpt.ae_ne_zero_c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:58:44.683036+00:00
-- url     : https://prove2.me/submissions/c71b03e3-a4b6-49b1-9835-a637d873d1a6

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_DiscreteGroupWaves_IntegralEqOfSqrtCauchy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.NFCpt
open MeasureTheory Filter Topology
namespace CompanionTheory.NFCpt
theorem _root_.solution : ∀ᵐ t : ℂ, t ≠ 0 := by
  rw [ae_iff]
  simp
end CompanionTheory.NFCpt
