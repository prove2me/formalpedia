-- Prove2me | solution 1 for DiscreteConvex.MixedMatrices.konig_egervary_mixed_matrix
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:37:16.587987+00:00
-- url     : https://prove2.me/submissions/731834ae-edba-4441-becc-b4154859fcda

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedMatrix
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank
import Theorems.Thm_DiscreteConvex_MixedMatrices_exists_tight_pair

set_option autoImplicit false

open DiscreteConvex.MixedMatrices

theorem solution {R C K F : Type*} [Fintype R] [Fintype C] [Field K] [Field F]
    [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) (hA : IsMixedMatrix A Q T) :
    ∃ I : Finset R, ∃ J : Finset C,
      ((I.card : ℤ) + J.card - MatrixSubRank Q I J = Fintype.card R + Fintype.card C - A.rank) ∧
      MatrixSubRank T I J = 0 := by
  obtain ⟨I, J, hτ, hρ⟩ := exists_tight_pair A Q T hA
  refine ⟨I, J, ?_, hτ⟩
  have h1 := Finset.card_add_card_compl I
  have h2 := Finset.card_add_card_compl J
  omega

#print axioms solution
