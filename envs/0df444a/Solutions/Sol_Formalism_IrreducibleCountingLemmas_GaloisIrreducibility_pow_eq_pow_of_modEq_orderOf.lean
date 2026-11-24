-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.pow_eq_pow_of_modEq_orderOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:12:45.823387+00:00
-- url     : https://prove2.me/submissions/a0cea9da-c369-45cb-a3b8-9b3d60682769

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRPrimeToPartSpec

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
theorem _root_.solution {M : Type*} [Monoid M] (x : M) {a b : ℕ}
    (h : a ≡ b [MOD orderOf x]) : x ^ a = x ^ b := by
  rw [← pow_mod_orderOf x a, ← pow_mod_orderOf x b, show a % orderOf x = b % orderOf x from h]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
