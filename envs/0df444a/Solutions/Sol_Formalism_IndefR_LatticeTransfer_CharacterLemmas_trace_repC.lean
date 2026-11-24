-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.CharacterLemmas.trace_repC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:20.782429+00:00
-- url     : https://prove2.me/submissions/2014c87e-61a2-470c-9a4d-5e2b1ca8cb63

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_AllPartsTransfer
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_TraceOfDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.LatticeTransfer
open Formalism.IndefR.TransferLatticeStatement
open Formalism.IndefR.LatticeTransfer.CharacterLemmas
namespace Formalism.IndefR.LatticeTransfer.CharacterLemmas
theorem _root_.solution {K : Type} [Field K] (σ : K →+* ℂ) {G : Type} [Group G] {T : Type}
    [AddCommGroup T] [Module K T] [FiniteDimensional K T] (τ : Representation K G T) (g : G) :
    LinearMap.trace ℂ _ (repC σ τ g) = σ (charOf τ g) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin (finrank K T))), charOf,
    LinearMap.trace_eq_matrix_trace K (Module.finBasis K T) (τ g)]
  simp [repC, LinearMap.toMatrix_eq_toMatrix', Matrix.trace, map_sum, LinearMap.toMatrixAlgEquiv_apply,
    LinearMap.toMatrix_apply]
end Formalism.IndefR.LatticeTransfer.CharacterLemmas
