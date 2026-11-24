-- Prove2me | solution 1 for Formalism.SLP.P.gram_eq_of_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:37:23.861749+00:00
-- url     : https://prove2.me/submissions/5dd81d19-459c-43d6-ada2-0637be2be973

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
theorem _root_.solution {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {m : ℕ}
    (e : Fin m → V) (he : Orthonormal ℂ e) (A : Matrix (Fin m) (Fin m) ℂ) (u : Fin m → V)
    (hu : ∀ i, u i = ∑ k, A i k • e k) :
    Matrix.gram ℂ u = (A * Aᴴ)ᵀ := by
  ext i j
  rw [Matrix.gram_apply, hu i, hu j, he.inner_sum, Matrix.transpose_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, mul_comm]
  rfl
end Formalism.SLP.P
