-- Prove2me | solution 1 for DiscreteConvex.MixedMatrices.rank_le_matrixSubRank_add
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:37:01.682995+00:00
-- url     : https://prove2.me/submissions/1d79f1fc-151f-4953-8d2a-8a908d2943bd

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank
import Theorems.Thm_DiscreteConvex_MixedMatrices_matrixSubRank_map_algebraMap

set_option autoImplicit false

namespace DiscreteConvex.MixedMatrices

open Module Submodule Set

/-- Subadditivity of the rank. -/
theorem pk_rank_add_le {m n F : Type*} [Fintype m] [Fintype n] [Field F] (X Y : Matrix m n F) :
    (X + Y).rank ≤ X.rank + Y.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc finrank F (LinearMap.range (X.mulVecLin + Y.mulVecLin))
      ≤ finrank F ↥(LinearMap.range X.mulVecLin ⊔ LinearMap.range Y.mulVecLin) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _


/-- `rank M ≤ rank M[I, ·] + |Iᶜ|`. -/
theorem pk_rank_le_rows {R C F : Type*} [Fintype R] [Fintype C] [Field F] [DecidableEq R]
    (M : Matrix R C F) (I : Finset R) :
    M.rank ≤ (M.submatrix ((↑) : I → R) id).rank + Iᶜ.card := by
  classical
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row (M.submatrix _ _)]
  let S : Finset (C → F) := Iᶜ.image M.row
  have hS : S.card ≤ Iᶜ.card := Finset.card_image_le
  have hle : span F (range M.row)
      ≤ span F (range (M.submatrix ((↑) : I → R) id).row) ⊔ span F (S : Set (C → F)) := by
    refine span_le.2 ?_
    rintro _ ⟨i, rfl⟩
    by_cases hi : i ∈ I
    · exact Submodule.mem_sup_left (subset_span ⟨⟨i, hi⟩, rfl⟩)
    · exact Submodule.mem_sup_right (subset_span (Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_compl.2 hi, rfl⟩)))
  calc finrank F (span F (range M.row))
      ≤ finrank F ↥(span F (range (M.submatrix ((↑) : I → R) id).row) ⊔ span F (S : Set (C → F))) :=
        Submodule.finrank_mono hle
    _ ≤ finrank F (span F (range (M.submatrix ((↑) : I → R) id).row))
          + finrank F (span F (S : Set (C → F))) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ finrank F (span F (range (M.submatrix ((↑) : I → R) id).row)) + Iᶜ.card := by
        have := finrank_span_finset_le_card (R := F) S
        unfold Set.finrank at this
        omega


/-- `rank M ≤ rank M[·, J] + |Jᶜ|`. -/
theorem pk_rank_le_cols {R C F : Type*} [Fintype R] [Fintype C] [Field F] [DecidableEq C]
    (M : Matrix R C F) (J : Finset C) :
    M.rank ≤ (M.submatrix id ((↑) : J → C)).rank + Jᶜ.card := by
  have h := pk_rank_le_rows M.transpose J
  rwa [Matrix.rank_transpose, ← Matrix.transpose_submatrix, Matrix.rank_transpose] at h


/-- `rank M ≤ rank M[I,J] + |Iᶜ| + |Jᶜ|` for any matrix over a field. -/
theorem pk_rank_le_sub {R C F : Type*} [Fintype R] [Fintype C] [Field F] [DecidableEq R]
    [DecidableEq C] (M : Matrix R C F) (I : Finset R) (J : Finset C) :
    M.rank ≤ (M.submatrix ((↑) : I → R) ((↑) : J → C)).rank + Iᶜ.card + Jᶜ.card := by
  have h1 := pk_rank_le_rows M I
  have h2 := pk_rank_le_cols (M.submatrix ((↑) : I → R) id) J
  have h3 : (M.submatrix ((↑) : I → R) id).submatrix id ((↑) : J → C)
      = M.submatrix ((↑) : I → R) ((↑) : J → C) := rfl
  rw [h3] at h2
  omega


/-- Weak duality for the first min-formula: `rank A ≤ ρ(I,J) + τ(I,J) + |R \ I| + |C \ J|`.
Only the entrywise decomposition `A = Q + T` is used (no genericity). -/
theorem pk_rank_le_matrixSubRank_add {R C K F : Type*} [Fintype R] [Fintype C] [Field K] [Field F]
    [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F)
    (hA : ∀ i j, A i j = algebraMap K F (Q i j) + T i j) (I : Finset R) (J : Finset C) :
    A.rank ≤ MatrixSubRank Q I J + MatrixSubRank T I J + Iᶜ.card + Jᶜ.card := by
  have h1 := pk_rank_le_sub A I J
  have hA' : A.submatrix ((↑) : I → R) ((↑) : J → C)
      = (Q.map (algebraMap K F)).submatrix ((↑) : I → R) ((↑) : J → C)
        + T.submatrix ((↑) : I → R) ((↑) : J → C) := by
    ext i j
    simp [hA]
  have h2 := pk_rank_add_le ((Q.map (algebraMap K F)).submatrix ((↑) : I → R) ((↑) : J → C))
    (T.submatrix ((↑) : I → R) ((↑) : J → C))
  have h3 := matrixSubRank_map_algebraMap (F := F) Q I J
  unfold MatrixSubRank at h3 ⊢
  rw [hA'] at h1
  omega

end DiscreteConvex.MixedMatrices

open DiscreteConvex.MixedMatrices

theorem solution {R C K F : Type*} [Fintype R] [Fintype C] [Field K] [Field F]
    [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F)
    (hA : ∀ i j, A i j = algebraMap K F (Q i j) + T i j) (I : Finset R) (J : Finset C) :
    A.rank ≤ MatrixSubRank Q I J + MatrixSubRank T I J + Iᶜ.card + Jᶜ.card :=
  pk_rank_le_matrixSubRank_add A Q T hA I J

#print axioms solution
