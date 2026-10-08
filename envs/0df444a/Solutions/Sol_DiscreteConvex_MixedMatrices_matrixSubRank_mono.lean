-- Prove2me | solution 1 for DiscreteConvex.MixedMatrices.matrixSubRank_mono
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:36:59.653222+00:00
-- url     : https://prove2.me/submissions/4a6541e2-467d-4a5e-a8b5-df58aa581289

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank

set_option autoImplicit false

namespace DiscreteConvex.MixedMatrices

open Module Submodule Set

/-- Monotonicity of `MatrixSubRank` in both index sets. -/
theorem pk_matrixSubRank_mono {R C 𝔽 : Type*} [Fintype R] [Fintype C] [Field 𝔽]
    (M : Matrix R C 𝔽) {I I' : Finset R} {J J' : Finset C} (hI : I ⊆ I') (hJ : J ⊆ J') :
    MatrixSubRank M I J ≤ MatrixSubRank M I' J' := by
  unfold MatrixSubRank
  have h : M.submatrix ((↑) : I → R) ((↑) : J → C)
      = (M.submatrix ((↑) : I' → R) ((↑) : J' → C)).submatrix
          (fun i : I => (⟨i.1, hI i.2⟩ : I')) (fun j : J => (⟨j.1, hJ j.2⟩ : J')) := rfl
  rw [h]
  exact Matrix.rank_submatrix_le _ _ _

end DiscreteConvex.MixedMatrices

open DiscreteConvex.MixedMatrices

theorem solution {R C 𝔽 : Type*} [Fintype R] [Fintype C] [Field 𝔽]
    (M : Matrix R C 𝔽) {I I' : Finset R} {J J' : Finset C} (hI : I ⊆ I') (hJ : J ⊆ J') :
    MatrixSubRank M I J ≤ MatrixSubRank M I' J' :=
  pk_matrixSubRank_mono M hI hJ

#print axioms solution
