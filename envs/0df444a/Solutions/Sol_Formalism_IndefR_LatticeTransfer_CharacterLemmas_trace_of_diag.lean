-- Prove2me | solution 1 for Formalism.IndefR.LatticeTransfer.CharacterLemmas.trace_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:20.735247+00:00
-- url     : https://prove2.me/submissions/0d228073-cb9b-49cd-bce0-a8feeb10df48

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
theorem _root_.solution {V I : Type*} [AddCommGroup V] [Module ℂ V] [Fintype I] [DecidableEq I]
    (v : Basis I ℂ V) (h : V →ₗ[ℂ] V) (c : I → ℂ) (hv : ∀ i, h (v i) = c i • v i) :
    LinearMap.trace ℂ V h = ∑ i, c i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ v h, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hv i, map_smul, Basis.repr_self]
  simp
end Formalism.IndefR.LatticeTransfer.CharacterLemmas
