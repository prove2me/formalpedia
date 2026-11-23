-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:24.913707+00:00
-- url     : https://prove2.me/submissions/78a6e6c2-ad12-4b0b-9920-0e5d0b898a1f

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
theorem _root_.solution [Fintype Γ] (τ : FDRep ℂ Γ) (γ : Γ) :
    (zIdem τ).coeff γ = (Module.finrank ℂ τ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ τ (τ.ρ γ⁻¹) := by
  classical
  unfold zIdem
  simp [MonoidAlgebra.coeff, Finsupp.finset_sum_apply, Finsupp.single_apply, MonoidAlgebra.single]
end Formalism.IrreducibleCountingLemmas.TYPES
