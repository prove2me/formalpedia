-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.flip_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:50:46.085782+00:00
-- url     : https://prove2.me/submissions/5af4e7ef-9324-477c-b72f-ec4b1e8e9a83

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_LocalEstimateIVOfTypeSetWeight
import Definitions.Def_Lemmata_TwistedIdempotents_TwistedIdem
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_MemBesselSetZeroIffUpperTriangular
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_uniChar_val
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_IsUT_flip
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_edgeSum_flip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
variable {K : Type} [Field K] {N : ℕ}
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution (ψ₀ : AddChar K ℂ) (u : uniSub K N) :
    ∃ h : flipG (u : GL (Fin N) K) ∈ uniSub K N, uniChar ψ₀ N ⟨flipG u, h⟩ = uniChar ψ₀ N u := by
  refine ⟨IsUT.flip u.2, ?_⟩
  apply Units.ext
  rw [uniChar_val, uniChar_val]
  show ψ₀ (edgeSum (flipM _)) = _
  rw [edgeSum_flip]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
