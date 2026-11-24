-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.trace_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:52:07.646866+00:00
-- url     : https://prove2.me/submissions/204c68f6-86db-4bf2-ac4e-39ff2532882e

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {V I : Type*} [AddCommGroup V] [Module ℂ V] [Fintype I] [DecidableEq I]
    (v : Basis I ℂ V) (h : V →ₗ[ℂ] V) (c : I → ℂ) (hv : ∀ i, h (v i) = c i • v i) :
    LinearMap.trace ℂ V h = ∑ i, c i := by
  rw [LinearMap.trace_eq_matrix_trace ℂ v h, Matrix.trace]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, hv i, map_smul, Finsupp.smul_apply,
    Basis.repr_self, Finsupp.single_eq_same, smul_eq_mul, mul_one]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
