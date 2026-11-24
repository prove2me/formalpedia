-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.pow_lpow_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:50:58.796801+00:00
-- url     : https://prove2.me/submissions/5872e873-6e90-479b-b8b8-7fd39000d2cd

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartEqIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {M : Type*} [Monoid M] {l a : ℕ} {x z : M} (h : x ^ (l ^ a) = z ^ (l ^ a))
    (b : ℕ) : x ^ (l ^ (a + b)) = z ^ (l ^ (a + b)) := by
  rw [pow_add, pow_mul, pow_mul, h]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
