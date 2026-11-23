-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.Idx.ord_unit_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:49.611509+00:00
-- url     : https://prove2.me/submissions/238e4430-af24-4420-996b-743e5ccb77c0

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive

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
open Formalism.IrreducibleCountingLemmas.TW.Idx
variable {O K V : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
  [IsScalarTower O K V]
namespace Formalism.IrreducibleCountingLemmas.TW.Idx
theorem _root_.solution {ϖ : O} (hϖ : Irreducible ϖ) (u : Oˣ) (n : ℕ) :
    Ring.ord O ((u : O) * ϖ ^ n) = n := by
  rw [Ring.ord_mul_of_isUnit_left u.isUnit,
    Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero), Ring.ord_of_irreducible hϖ]
  simp
end Formalism.IrreducibleCountingLemmas.TW.Idx
