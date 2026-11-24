-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TYPES.finrank_bc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:52:06.912204+00:00
-- url     : https://prove2.me/submissions/ed64766b-0079-4a61-bfe4-360dd264c2c4

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial CategoryTheory
noncomputable section
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TYPES
variable {Γ : Type} [Group Γ]
namespace Formalism.IrreducibleCountingLemmas.TYPES
theorem _root_.solution (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) :
    Module.finrank ℂ (bc σ τ) = Module.finrank ℂ τ := by
  exact Module.finrank_fin_fun ℂ
end Formalism.IrreducibleCountingLemmas.TYPES
