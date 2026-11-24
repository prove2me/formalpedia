-- Prove2me | solution 1 for Formalism.SLP.P.norm_det_gram_of_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:47:45.3723+00:00
-- url     : https://prove2.me/submissions/de0005a6-56ff-4570-8c8b-90a25931d035

import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_GelfandTransference_HadamardGelfand_Hadamard
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_SesquilinearDeterminantHolds
import Theorems.Thm_Formalism_SLP_P_gram_eq_of_decomp

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
    ‖(Matrix.gram ℂ u).det‖ = ‖A.det‖ ^ 2 := by
  rw [gram_eq_of_decomp e he A u hu, Matrix.det_transpose, Matrix.det_mul, Matrix.det_conjTranspose,
    norm_mul, norm_star, sq]
end Formalism.SLP.P
