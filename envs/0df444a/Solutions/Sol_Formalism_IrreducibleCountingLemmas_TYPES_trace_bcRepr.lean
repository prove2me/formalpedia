-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.TYPES.trace_bcRepr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T09:52:08.494917+00:00
-- url     : https://prove2.me/submissions/b156d579-5c82-4262-aa63-d42842895820

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
theorem _root_.solution (σ : ℂ ≃+* ℂ) {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ Γ V) (γ : Γ) :
    LinearMap.trace ℂ _ (bcRepr σ ρ γ) = σ (LinearMap.trace ℂ V (ρ γ)) := by
  have h1 : bcRepr σ ρ γ = Matrix.toLin' (σ.toRingHom.mapMatrix
      (LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) (ρ γ))) := rfl
  rw [h1, LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ _), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin', LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V) (ρ γ)]
  simp [Matrix.trace, map_sum]
end Formalism.IrreducibleCountingLemmas.TYPES
