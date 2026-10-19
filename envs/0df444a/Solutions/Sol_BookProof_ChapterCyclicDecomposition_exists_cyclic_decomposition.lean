-- Prove2me | solution 1 for BookProof.ChapterCyclicDecomposition.exists_cyclic_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T01:51:29.957962+00:00
-- url     : https://prove2.me/submissions/e5d17412-a84c-4475-a5fa-f8aa141e2f89

-- Generated from ChapterCyclicDecomposition.lean — solution of BookProof.ChapterCyclicDecomposition.exists_cyclic_decomposition
import Mathlib
import Definitions.Def_ChapterCyclicDecomposition
import Theorems.Thm_BookProof_ChapterCyclicDecomposition_self_mem_cyclicSubspace
import Theorems.Thm_BookProof_ChapterCyclicDecomposition_cyclicSubspace_le_orthogonal
import Theorems.Thm_BookProof_ChapterCyclicDecomposition_invariant_iSup_cyclicSubspace
import Definitions.Def_ChapterSpectralMultiplication
open BookProof.ChapterCyclicDecomposition



noncomputable section

open MeasureTheory Complex


open BookProof.ChapterSpectralMultiplication

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T : H →L[ℂ] H) (hT : IsStarNormal T)

set_option maxHeartbeats 1000000 in
theorem solution :
    ∃ S : Set H, OrthogonalCyclicFamily T hT S ∧
      (⨆ x ∈ S, cyclicSubspace T hT x).topologicalClosure = ⊤ := by

  obtain ⟨S, hS⟩ :=
    zorn_subset {S : Set H | OrthogonalCyclicFamily T hT S} (fun c hc hchain => by
      refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
      · rintro x ⟨s, hs, hx⟩
        exact ((hc hs).1) x hx
      · rintro x ⟨s, hs, hx⟩ y ⟨t, ht, hy⟩ hxy
        rcases hchain.total hs ht with h | h
        · exact ((hc ht).2) x (h hx) y hy hxy
        · exact ((hc hs).2) x hx y (h hy) hxy)
  refine ⟨S, hS.1, ?_⟩
  set N : Submodule ℂ H := ⨆ x ∈ S, cyclicSubspace T hT x with hN
  haveI : CompleteSpace N.topologicalClosure :=
    (Submodule.isClosed_topologicalClosure N).completeSpace_coe
  by_contra hne
  have hbot : N.topologicalClosureᗮ ≠ ⊥ := by
    intro h
    exact hne (Submodule.orthogonal_eq_bot_iff.1 h)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  set u : H := ‖v‖⁻¹ • v with hu
  have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  have hunorm : ‖u‖ = 1 := by
    rw [hu, norm_smul]
    simp [hnv]
  have humem : u ∈ N.topologicalClosureᗮ := Submodule.smul_mem _ _ hv
  -- the cyclic subspace of `u` is orthogonal to everything already collected
  have hcyc : cyclicSubspace T hT u ≤ N.topologicalClosureᗮ :=
    cyclicSubspace_le_orthogonal T hT (invariant_iSup_cyclicSubspace T hT S) humem
  have hle : ∀ x ∈ S, cyclicSubspace T hT x ≤ N.topologicalClosure := fun x hx =>
    le_trans (le_iSup₂ (f := fun x (_ : x ∈ S) => cyclicSubspace T hT x) x hx)
      (Submodule.le_topologicalClosure N)
  have hnew : (insert u S) ∈ {S : Set H | OrthogonalCyclicFamily T hT S} := by
    constructor
    · rintro x (rfl | hx)
      · exact hunorm
      · exact hS.1.1 x hx
    · have key : ∀ x ∈ S, cyclicSubspace T hT u ≤ (cyclicSubspace T hT x)ᗮ := fun x hx =>
        le_trans hcyc (Submodule.orthogonal_le (hle x hx))
      have key' : ∀ x ∈ S, cyclicSubspace T hT x ≤ (cyclicSubspace T hT u)ᗮ := fun x hx =>
        le_trans (le_trans (hle x hx) (Submodule.le_orthogonal_orthogonal _))
          (Submodule.orthogonal_le hcyc)
      rintro x (rfl | hx) y (rfl | hy) hxy
      · exact absurd rfl hxy
      · exact key y hy
      · exact key' x hx
      · exact hS.1.2 x hx y hy hxy
  have hnotmem : u ∉ S := by
    intro hmem
    have h1 : u ∈ N.topologicalClosure := hle u hmem (self_mem_cyclicSubspace T hT u)
    have : u = 0 := inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 humem u h1)
    rw [this] at hunorm
    simp at hunorm
  exact hnotmem (hS.2 hnew (Set.subset_insert u S) (Set.mem_insert u S))
