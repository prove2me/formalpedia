-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.det_sesquilinear_change_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:33.877989+00:00
-- url     : https://prove2.me/submissions/5ff256b4-b86e-4d9c-866c-34bc554036c5

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open InnerProductSpace
variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) {j : ℕ} (L L' : Matrix (Fin j) (Fin j) ℂ) (g : Fin j → V₁)
    (g' : Fin j → V₂) :
    (Matrix.of fun a b => B (∑ i, L a i • g i) (∑ k, L' b k • g' k)).det =
      L.det * (Matrix.of fun i k => B (g i) (g' k)).det * star L'.det := by
  have : (Matrix.of fun a b => B (∑ i, L a i • g i) (∑ k, L' b k • g' k)) =
      L * (Matrix.of fun i k => B (g i) (g' k)) * L'ᴴ := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
      LinearMap.sum_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
end Formalism.HermitianLatticeCounting.P
