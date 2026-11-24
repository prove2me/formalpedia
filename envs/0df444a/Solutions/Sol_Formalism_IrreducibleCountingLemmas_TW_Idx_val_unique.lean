-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.Idx.val_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T09:59:42.214224+00:00
-- url     : https://prove2.me/submissions/b49bbf8a-7006-40b1-92c1-37507e32ce33

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexDet
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_valuation_unique

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
theorem _root_.solution {ϖ : O} (hϖ : Irreducible ϖ) (u v : Oˣ) (a b : ℤ)
    (h : algebraMap O K u * algebraMap O K ϖ ^ a = algebraMap O K v * algebraMap O K ϖ ^ b) :
    a = b := by
  rcases le_total a b with hab | hab
  · obtain ⟨m, rfl⟩ := Int.le.dest hab
    have := valuation_unique hϖ u v a m h
    simp [this]
  · obtain ⟨m, rfl⟩ := Int.le.dest hab
    have := valuation_unique hϖ v u b m h.symm
    simp [this]
end Formalism.IrreducibleCountingLemmas.TW.Idx
