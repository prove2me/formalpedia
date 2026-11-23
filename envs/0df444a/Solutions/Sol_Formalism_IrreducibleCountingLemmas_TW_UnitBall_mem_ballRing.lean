-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.UnitBall.mem_ballRing
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:50.723336+00:00
-- url     : https://prove2.me/submissions/cae43d25-fddc-4abb-a4bf-e182248fc045

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWUnitBallLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
open Formalism.IrreducibleCountingLemmas.TW.UnitBall
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]
namespace Formalism.IrreducibleCountingLemmas.TW.UnitBall
theorem _root_.solution (x : K) : x ∈ ballRing K ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
  exact_mod_cast Iff.rfl
end Formalism.IrreducibleCountingLemmas.TW.UnitBall
