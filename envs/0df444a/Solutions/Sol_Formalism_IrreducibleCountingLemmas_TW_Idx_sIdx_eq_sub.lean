-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TW.Idx.sIdx_eq_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:28:40.001219+00:00
-- url     : https://prove2.me/submissions/26e5a29f-3f7a-4b3c-88a6-3e127e983f72

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWIndexAdditive
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_relLen_inf
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_relLen_tower
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_isLat_inf
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_Idx_relLen_ne_top

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
variable [FiniteDimensional K V]
namespace Formalism.IrreducibleCountingLemmas.TW.Idx
theorem _root_.solution {M N Q : Submodule O V} (hM : IsLat O K M) (hN : IsLat O K N)
    (hQ : IsLat O K Q) (hQM : Q ≤ M) (hQN : Q ≤ N) :
    sIdx M N = ((relLen M Q).toNat : ℤ) - ((relLen N Q).toNat : ℤ) := by
  have h1 := relLen_tower (le_inf hQM hQN) (inf_le_left : M ⊓ N ≤ M)
  have h2 := relLen_tower (le_inf hQM hQN) (inf_le_right : M ⊓ N ≤ N)
  rw [relLen_inf] at h1
  rw [inf_comm, relLen_inf] at h2
  have f0 := relLen_ne_top (isLat_inf hN hM) hQ
  have f1 := relLen_ne_top hM hN
  have f2 := relLen_ne_top hN hM
  rw [inf_comm] at h1
  unfold sIdx
  rw [h1, h2, ENat.toNat_add f0 f1, ENat.toNat_add f0 f2]
  push_cast
  ring
end Formalism.IrreducibleCountingLemmas.TW.Idx
