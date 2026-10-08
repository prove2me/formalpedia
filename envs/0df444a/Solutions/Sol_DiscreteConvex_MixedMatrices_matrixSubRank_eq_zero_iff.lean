-- Prove2me | solution 1 for DiscreteConvex.MixedMatrices.matrixSubRank_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:36:55.41425+00:00
-- url     : https://prove2.me/submissions/a145bfaf-5909-4ef7-810f-b83da7e77f66

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank

set_option autoImplicit false

namespace DiscreteConvex.MixedMatrices

open Module Submodule Set

/-- `Q[I,J]` has rank zero iff it is the zero matrix. -/
theorem pk_matrixSubRank_eq_zero_iff {R C 𝔽 : Type*} [Fintype R] [Fintype C] [Field 𝔽]
    (M : Matrix R C 𝔽) (I : Finset R) (J : Finset C) :
    MatrixSubRank M I J = 0 ↔ ∀ i ∈ I, ∀ j ∈ J, M i j = 0 := by
  unfold MatrixSubRank
  rw [Matrix.rank_eq_finrank_span_cols, Submodule.finrank_eq_zero, Submodule.span_eq_bot]
  constructor
  · intro h i hi j hj
    have := h _ ⟨⟨j, hj⟩, rfl⟩
    exact congrFun this ⟨i, hi⟩
  · rintro h x ⟨j, rfl⟩
    funext i
    exact h _ i.2 _ j.2

end DiscreteConvex.MixedMatrices

open DiscreteConvex.MixedMatrices

theorem solution {R C 𝔽 : Type*} [Fintype R] [Fintype C] [Field 𝔽]
    (M : Matrix R C 𝔽) (I : Finset R) (J : Finset C) :
    MatrixSubRank M I J = 0 ↔ ∀ i ∈ I, ∀ j ∈ J, M i j = 0 :=
  pk_matrixSubRank_eq_zero_iff M I J

#print axioms solution
