-- Prove2me | solution 1 for DiazModulus.matrix_rank_map_field
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-11-14T14:10:30.239032+00:00
-- url     : https://prove2.me/submissions/624c9ab1-c676-428c-af0a-b6f900da33c4

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

/-! # The rank of a matrix is unchanged by a homomorphism of fields

Let `f : K → L` be a homomorphism of fields; it is injective, and it makes `L` a `K`-algebra.
The rank of `A` is the dimension of its row space. Choose rows `A_{i₁}, …, A_{i_r}` forming a
`K`-basis of the row space, so `r = rank A`. Their images `f(A_{i₁}), …, f(A_{i_r})` are rows of
`f(A)`, and they are `L`-linearly independent, because `K`-free vectors of `K^ℓ` stay free over
the extension `L`. Every row satisfies `A_j = Σ_s c_{js} A_{i_s}` with `c_{js} ∈ K`, so applying
`f` entrywise gives `f(A_j) = Σ_s f(c_{js}) f(A_{i_s})`. Hence the chosen image rows are an
`L`-basis of the row space of `f(A)`, whose dimension is again `r`. -/

namespace RC4_RMF
open DiazModulus
end RC4_RMF

open DiazModulus RC4_RMF in
theorem solution {K L : Type*} [Field K] [Field L] (f : K →+* L) {d l : ℕ}
    (A : Matrix (Fin d) (Fin l) K) : (A.map f).rank = A.rank := by
  classical
  let : Algebra K L := f.toAlgebra
  have : FaithfulSMul K L := (faithfulSMul_iff_algebraMap_injective K L).mpr f.injective
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.row
  have : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  -- the chosen rows stay free over `L`
  have hli' : LinearIndependent L ((A.map f).row ∘ a) :=
    (linearIndependent_algebraMap_comp_iff (R := K) (S := L) (v := A.row ∘ a)).mpr hli
  -- and they still span the row space
  have hspan' : Submodule.span L (Set.range ((A.map f).row ∘ a)) =
      Submodule.span L (Set.range (A.map f).row) := by
    apply le_antisymm (Submodule.span_mono (Set.range_comp_subset_range _ _))
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have hj : A.row j ∈ Submodule.span K (Set.range (A.row ∘ a)) := by
      rw [hspan]; exact Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hj
    refine (Submodule.mem_span_range_iff_exists_fun L).mpr ⟨fun s => f (c s), ?_⟩
    funext col
    have h := congrFun hc col
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply,
      Matrix.row_apply] at h ⊢
    simp only [Matrix.map_apply, ← h, map_sum, map_mul]
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row, ← hspan, ← hspan',
    finrank_span_eq_card hli, finrank_span_eq_card hli']
