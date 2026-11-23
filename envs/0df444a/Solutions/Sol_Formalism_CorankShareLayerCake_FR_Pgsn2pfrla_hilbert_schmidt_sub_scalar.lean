-- Prove2me | solution 1 for Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.hilbert_schmidt_sub_scalar
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:36:12.971218+00:00
-- url     : https://prove2.me/submissions/c48fee26-8161-409e-8f8d-88073d6ac98c

import Mathlib
import Definitions.Def_Formalism_CorankShare_StatementFR
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
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
theorem _root_.solution (c : ι → ℝ) (B : ∀ i, V i →ₗ[ℂ] H) (lam : ℝ) :
    hs2 (frQ c B - (lam : ℂ) • LinearMap.id) =
      (trace ℂ H (frQ c B ∘ₗ frQ c B)).re - 2 * lam * (trace ℂ H (frQ c B)).re
        + lam ^ 2 * finrank ℂ H := by
  have hadj : frQ c B - (lam : ℂ) • LinearMap.id = adjoint (frQ c B - (lam : ℂ) • LinearMap.id) := by
    rw [LinearMap.eq_adjoint_iff]
    intro x y
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal, Q_symm c B x y]
  unfold hs2
  rw [← hadj]
  simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.id_comp,
    LinearMap.comp_id, map_sub, map_smul, LinearMap.trace_id, smul_eq_mul, Complex.sub_re, Complex.re_ofReal_mul,
    Complex.natCast_re]
  ring
end Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
