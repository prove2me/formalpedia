-- Prove2me | solution 1 for Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.trace_frame_sq_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:13.432938+00:00
-- url     : https://prove2.me/submissions/fae44048-5f1b-455c-b285-18be13321df6

import Mathlib
import Definitions.Def_Formalism_CorankShare_StatementFR
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_hilbert_schmidt_eq_basis_sum
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_Q_symm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.CorankShareLayerCake Formalism.CorankShareLayerCake.FR
open Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
open Finset Module LinearMap
open scoped InnerProductSpace
variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)]
    [∀ i, InnerProductSpace ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
namespace Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
theorem _root_.solution (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) :
    (trace ℂ H (frQ c B ∘ₗ frQ c B)).re = ∑ n, ‖frQ c B (stdOrthonormalBasis ℂ H n)‖ ^ 2 := by
  have hadj : frQ c B = adjoint (frQ c B) := by
    rw [LinearMap.eq_adjoint_iff]; exact Q_symm c B
  have h := hilbert_schmidt_eq_basis_sum (frQ c B) (stdOrthonormalBasis ℂ H)
  unfold hs2 at h
  rw [← hadj] at h
  exact h
end Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
