-- Prove2me | solution 1 for DiscreteConvex.MixedMatrices.matrixSubRank_map_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:36:53.954029+00:00
-- url     : https://prove2.me/submissions/9d289ae9-53e9-43bb-b927-edc41f4cd170

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank

set_option autoImplicit false

namespace DiscreteConvex.MixedMatrices

open Module Submodule Set

/-- The rank of a matrix over a field does not change under a field extension. -/
theorem pk_rank_map {m n K F : Type*} [Fintype m] [Fintype n] [Field K] [Field F] [Algebra K F]
    (M : Matrix m n K) : (M.map (algebraMap K F)).rank = M.rank := by
  have hcol : ∀ j, (M.map (algebraMap K F)).col j = algebraMap K F ∘ M.col j := fun j => rfl
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  apply le_antisymm
  · obtain ⟨b, hb, hspan, hli⟩ :=
      exists_linearIndependent F (Set.range (M.map (algebraMap K F)).col)
    have : Finite b := (Set.finite_range _).subset hb
    have : Fintype b := Fintype.ofFinite b
    have hj : ∀ x : b, ∃ j, (M.map (algebraMap K F)).col j = x.1 := fun x => hb x.2
    choose j hj using hj
    have hcomp : (fun x : b => algebraMap K F ∘ M.col (j x)) = ((↑) : b → (m → F)) := by
      funext x
      rw [← hcol, hj]
    have hv : LinearIndependent K (fun x : b => M.col (j x)) := by
      rw [← linearIndependent_algebraMap_comp_iff (S := F), hcomp]
      exact hli
    calc finrank F (span F (range (M.map (algebraMap K F)).col)) = finrank F (span F b) := by
          rw [hspan]
      _ = Fintype.card b := by
          have h := finrank_span_eq_card hli
          rwa [Subtype.range_coe] at h
      _ = finrank K (span K (range fun x : b => M.col (j x))) := (finrank_span_eq_card hv).symm
      _ ≤ finrank K (span K (range M.col)) :=
          Submodule.finrank_mono (span_mono (by rintro _ ⟨x, rfl⟩; exact ⟨j x, rfl⟩))
  · obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent K (Set.range M.col)
    have : Finite b := (Set.finite_range _).subset hb
    have : Fintype b := Fintype.ofFinite b
    have hj : ∀ x : b, ∃ j, M.col j = x.1 := fun x => hb x.2
    choose j hj using hj
    have hF : LinearIndependent F (fun x : b => (M.map (algebraMap K F)).col (j x)) := by
      have : (fun x : b => (M.map (algebraMap K F)).col (j x))
          = fun x : b => algebraMap K F ∘ (x.1 : m → K) := by
        funext x
        rw [hcol, hj]
      rw [this, linearIndependent_algebraMap_comp_iff (S := F)]
      exact hli
    calc finrank K (span K (range M.col)) = finrank K (span K b) := by rw [hspan]
      _ = Fintype.card b := by
          have h := finrank_span_eq_card hli
          rwa [Subtype.range_coe] at h
      _ = finrank F (span F (range fun x : b => (M.map (algebraMap K F)).col (j x))) :=
          (finrank_span_eq_card hF).symm
      _ ≤ finrank F (span F (range (M.map (algebraMap K F)).col)) :=
          Submodule.finrank_mono (span_mono (by rintro _ ⟨x, rfl⟩; exact ⟨j x, rfl⟩))


/-- Rank does not change under a field extension (applied to submatrices). -/
theorem pk_matrixSubRank_map_algebraMap {R C K F : Type*} [Fintype R] [Fintype C] [Field K]
    [Field F] [Algebra K F] (Q : Matrix R C K) (I : Finset R) (J : Finset C) :
    MatrixSubRank (Q.map (algebraMap K F)) I J = MatrixSubRank Q I J := by
  unfold MatrixSubRank
  rw [Matrix.submatrix_map]
  exact pk_rank_map _

end DiscreteConvex.MixedMatrices

open DiscreteConvex.MixedMatrices

theorem solution {R C K F : Type*} [Fintype R] [Fintype C] [Field K]
    [Field F] [Algebra K F] (Q : Matrix R C K) (I : Finset R) (J : Finset C) :
    MatrixSubRank (Q.map (algebraMap K F)) I J = MatrixSubRank Q I J :=
  pk_matrixSubRank_map_algebraMap Q I J

#print axioms solution
