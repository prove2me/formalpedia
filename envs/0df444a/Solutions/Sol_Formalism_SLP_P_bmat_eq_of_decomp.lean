-- Prove2me | solution 1 for Formalism.SLP.P.bmat_eq_of_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:19.992179+00:00
-- url     : https://prove2.me/submissions/fd1f3b94-5bc0-493c-89f6-450f593bdd72

import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Hadamard
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SesquilinearDeterminantHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset ComplexConjugate
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂]
namespace Formalism.SLP.P
theorem _root_.solution (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) {m : ℕ} (e : Fin m → V₁) (f : Fin m → V₂)
    (A C : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → V₁) (w : Fin m → V₂)
    (hu : ∀ i, u i = ∑ k, A i k • e k) (hw : ∀ j, w j = ∑ l, C j l • f l) :
    (Matrix.of fun i j => B (u i) (w j)) = A * (Matrix.of fun k l => B (e k) (f l)) * Cᴴ := by
  ext i j
  rw [Matrix.of_apply, hu i, hw j, Matrix.mul_apply]
  simp only [map_sum, LinearMap.map_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ,
    Matrix.mul_apply, Matrix.of_apply, Matrix.conjTranspose_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum,
    starRingEnd_apply, RingHom.id_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring
end Formalism.SLP.P
