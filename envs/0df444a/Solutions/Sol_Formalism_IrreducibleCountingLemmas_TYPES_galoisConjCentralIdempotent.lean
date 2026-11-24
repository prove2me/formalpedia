-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TYPES.galoisConjCentralIdempotent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:02:29.001801+00:00
-- url     : https://prove2.me/submissions/7ed249c3-f426-4e3a-972e-d42074c79dd4

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_IsConstituent
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisConjCentralIdempotent
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TYPES_trace_bcRepr
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TYPES_finrank_bc
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_TYPES_zIdem_coeff

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
variable (K : Type) [Field K] [Fintype K] [DecidableEq K]
namespace Formalism.IrreducibleCountingLemmas.TYPES
theorem _root_.solution : BcZIdem := by
  intro Γ _ _ σ τ γ
  have h : LinearMap.trace ℂ (bc σ τ) ((bc σ τ).ρ γ⁻¹) = σ (LinearMap.trace ℂ τ (τ.ρ γ⁻¹)) :=
    trace_bcRepr σ τ.ρ γ⁻¹
  rw [zIdem_coeff, zIdem_coeff, finrank_bc, h, map_mul, map_div₀, map_natCast, map_natCast]
end Formalism.IrreducibleCountingLemmas.TYPES
