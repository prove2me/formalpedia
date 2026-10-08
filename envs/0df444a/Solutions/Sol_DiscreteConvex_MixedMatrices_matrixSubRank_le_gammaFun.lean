-- Prove2me | solution 1 for DiscreteConvex.MixedMatrices.matrixSubRank_le_gammaFun
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:36:58.266999+00:00
-- url     : https://prove2.me/submissions/7cb1ea65-5887-4ff1-a9ad-3d3ffa16c4f4

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank
import Definitions.Def_DiscreteConvex_MixedMatrices_GammaFun

set_option autoImplicit false

namespace DiscreteConvex.MixedMatrices

open Module Submodule Set

/-- `τ(I,J) ≤ γ(I,J)`: the rank of `T[I,J]` is at most its number of nonzero rows. -/
theorem pk_matrixSubRank_le_gammaFun {R C F : Type*} [Fintype R] [Fintype C] [Field F]
    (T : Matrix R C F) (I : Finset R) (J : Finset C) :
    MatrixSubRank T I J ≤ GammaFun T I J := by
  classical
  unfold MatrixSubRank GammaFun
  set s : Finset I := Finset.univ.filter (fun i : I => ∃ j ∈ J, T i j ≠ 0) with hs
  have h1 : (T.submatrix ((↑) : I → R) ((↑) : J → C)).rank ≤ s.card := by
    refine Matrix.rank_le_card_of_support_subset _ s ?_
    intro i hi
    by_contra hns
    apply hi
    funext j
    have : ¬ ∃ j ∈ J, T i j ≠ 0 := fun h => hns (by simp [hs, h])
    push Not at this
    exact this j.1 j.2
  have h2 : s.card = (I.filter (fun i => ∃ j ∈ J, T i j ≠ 0)).card := by
    refine Finset.card_nbij (fun i => i.1) ?_ ?_ ?_
    · intro a ha
      simpa [hs] using ha
    · intro a _ b _ hab
      exact Subtype.ext hab
    · intro b hb
      have hb' := (Finset.mem_filter.1 (Finset.mem_coe.1 hb))
      exact ⟨⟨b, hb'.1⟩, Finset.mem_coe.2 (by simpa [hs] using hb'.2), rfl⟩
  rw [← h2]
  exact h1

end DiscreteConvex.MixedMatrices

open DiscreteConvex.MixedMatrices

theorem solution {R C F : Type*} [Fintype R] [Fintype C] [Field F]
    (T : Matrix R C F) (I : Finset R) (J : Finset C) :
    MatrixSubRank T I J ≤ GammaFun T I J :=
  pk_matrixSubRank_le_gammaFun T I J

#print axioms solution
