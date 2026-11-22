-- Prove2me | solution 1 for Formalism.CorankShareLayerCake.FR.Pgsn2pfrla.tQ_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:35:06.873801+00:00
-- url     : https://prove2.me/submissions/787a50bf-041b-4a11-9970-ae8c4908cf36

import Mathlib
import Definitions.Def_Formalism_CorankShare_StatementFR
import Definitions.Def_Formalism_CorankShare_CorankShareProofs_SumNormSqLeHilbertSchmidt
import Theorems.Thm_Formalism_CorankShareLayerCake_FR_Pgsn2pfrla_hilbert_schmidt_eq_basis_sum

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
    (trace ℂ H (frQ c B)).re = ∑ i, c i * ∑ m, ‖B i (stdOrthonormalBasis ℂ (V i) m)‖ ^ 2 := by
  simp only [frQ, map_sum, map_smul, smul_eq_mul, Complex.re_sum, Complex.re_ofReal_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 1
  rw [← hilbert_schmidt_eq_basis_sum (B i) (stdOrthonormalBasis ℂ (V i))]
  unfold hs2
  rw [LinearMap.trace_comp_comm']
end Formalism.CorankShareLayerCake.FR.Pgsn2pfrla
