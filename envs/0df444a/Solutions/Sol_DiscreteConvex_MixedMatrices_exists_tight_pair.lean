-- Prove2me | solution 1 for DiscreteConvex.MixedMatrices.exists_tight_pair
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-06T13:37:11.454616+00:00
-- url     : https://prove2.me/submissions/0bec2d0e-7ace-4a94-9e1e-d1a7d0576416

import Mathlib
import Definitions.Def_DiscreteConvex_MixedMatrices_IsMixedMatrix
import Definitions.Def_DiscreteConvex_MixedMatrices_MatrixSubRank
import Theorems.Thm_Rado_rado_defect
import Theorems.Thm_DiscreteConvex_MixedMatrices_finrank_span_cols_union_single
import Theorems.Thm_DiscreteConvex_MixedMatrices_card_le_rank_of_indep_transversal
import Theorems.Thm_DiscreteConvex_MixedMatrices_matrixSubRank_map_algebraMap
import Theorems.Thm_DiscreteConvex_MixedMatrices_matrixSubRank_eq_zero_iff
import Theorems.Thm_DiscreteConvex_MixedMatrices_rank_le_matrixSubRank_add

set_option autoImplicit false

open DiscreteConvex.MixedMatrices

theorem solution {R C K F : Type*} [Fintype R] [Fintype C] [Field K] [Field F]
    [Algebra K F] [DecidableEq R] [DecidableEq C]
    (A : Matrix R C F) (Q : Matrix R C K) (T : Matrix R C F) (hA : IsMixedMatrix A Q T) :
    ∃ (I : Finset R) (J : Finset C), MatrixSubRank T I J = 0 ∧
      MatrixSubRank Q I J + Iᶜ.card + Jᶜ.card = A.rank := by
  classical
  let Aset : C → Set (R → F) := fun c =>
    {fun r : R => algebraMap K F (Q r c)} ∪
      (fun s : R => (Pi.single s (1 : F) : R → F)) '' {s : R | T s c ≠ 0}
  have hfin : ∀ c, (Aset c).Finite := fun c =>
    (Set.finite_singleton _).union (Set.Finite.image _ (Set.toFinite _))
  obtain ⟨J₀, v, S, hv, hind, hcard⟩ := Rado.rado_defect (k := F) Aset hfin
  set N : Finset R := Finset.univ.filter (fun s => ∃ c ∈ S, T s c ≠ 0) with hN
  have hunion : (⋃ i ∈ S, Aset i) =
      ((fun c : C => (fun r : R => (Q.map (algebraMap K F)) r c)) '' (S : Set C)) ∪
        ((fun s : R => (Pi.single s (1 : F) : R → F)) '' (N : Set R)) := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_image,
      Set.mem_ofPred_eq, Finset.mem_coe, hN, Finset.mem_filter, Finset.mem_univ, true_and, Aset,
      Matrix.map_apply]
    constructor
    · rintro ⟨i, hi, h | ⟨s, hs, hsz⟩⟩
      · exact Or.inl ⟨i, hi, h.symm⟩
      · exact Or.inr ⟨s, ⟨i, hi, hs⟩, hsz⟩
    · rintro (⟨i, hi, h⟩ | ⟨s, ⟨i, hi, hs⟩, hsz⟩)
      · exact ⟨i, hi, Or.inl h.symm⟩
      · exact ⟨i, hi, Or.inr ⟨s, hs, hsz⟩⟩
  have hfr := finrank_span_cols_union_single (Q.map (algebraMap K F)) S N
  have hmap := matrixSubRank_map_algebraMap (F := F) Q Nᶜ S
  rw [hunion, hfr, hmap] at hcard
  have hT0 : MatrixSubRank T Nᶜ S = 0 := by
    refine (matrixSubRank_eq_zero_iff T Nᶜ S).2 ?_
    intro i hi c hc
    by_contra h
    exact (Finset.mem_compl.1 hi) (by simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨c, hc, h⟩)
  have h1 : J₀.card ≤ A.rank := card_le_rank_of_indep_transversal A Q T hA J₀ v hv hind
  have h2 := rank_le_matrixSubRank_add A Q T hA.1 Nᶜ S
  refine ⟨Nᶜ, S, hT0, ?_⟩
  rw [hT0, compl_compl] at h2
  rw [compl_compl]
  omega

#print axioms solution
