-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.Idx.relLen_ne_top_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:13:31.367503+00:00
-- url     : https://prove2.me/submissions/9c24aa7c-9ae9-4674-ba12-d72a43c97c79

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_exists_basis
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_relLen_span_of_le
import Theorems.Thm_P2M_Formalism_IrreducibleCountingLemmas_TW_Idx_ord_ne_top__57ca83d61db5

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
theorem _root_.solution {M N : Submodule O V} (hM : IsLat O K M) (hN : IsLat O K N)
    (hle : N ≤ M) : relLen M N ≠ ⊤ := by
  obtain ⟨n, β, rfl⟩ := exists_basis hM
  obtain ⟨n', γ, rfl⟩ := exists_basis hN
  have hn : n' = n := by
    have h1 := Module.finrank_eq_card_basis β
    have h2 := Module.finrank_eq_card_basis γ
    simpa using h2.symm.trans h1
  subst hn
  obtain ⟨D, hD, hlen⟩ := relLen_span_of_le (O := O) β γ hle (β.isUnit_det γ).ne_zero
  rw [hlen]
  apply ord_ne_top'
  rintro rfl
  rw [map_zero] at hD
  exact (β.isUnit_det γ).ne_zero hD.symm
end Formalism.IrreducibleCountingLemmas.TW.Idx
