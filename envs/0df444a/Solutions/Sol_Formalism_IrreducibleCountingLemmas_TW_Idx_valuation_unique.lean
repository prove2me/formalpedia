-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.Idx.valuation_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:52:09.312947+00:00
-- url     : https://prove2.me/submissions/f651b6d5-9404-4127-a1a4-066b90a80869

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexDet

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
variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]
namespace Formalism.IrreducibleCountingLemmas.TW.Idx
theorem _root_.solution {ϖ : O} (hϖ : Irreducible ϖ) (u v : Oˣ) (a : ℤ) (m : ℕ)
    (h : algebraMap O K u * algebraMap O K ϖ ^ a
      = algebraMap O K v * algebraMap O K ϖ ^ (a + (m : ℤ))) : m = 0 := by
  have hπ : algebraMap O K ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O K)).2 hϖ.ne_zero
  rw [zpow_add₀ hπ, zpow_natCast, mul_comm (_ ^ a), ← mul_assoc] at h
  have h2 := mul_right_cancel₀ (zpow_ne_zero a hπ) h
  rw [← map_pow, ← map_mul] at h2
  have h3 := IsFractionRing.injective O K h2
  by_contra hm
  have : IsUnit (ϖ ^ m) := isUnit_of_mul_isUnit_right (h3 ▸ u.isUnit)
  exact hϖ.not_isUnit ((isUnit_pow_iff hm).1 this)
end Formalism.IrreducibleCountingLemmas.TW.Idx
