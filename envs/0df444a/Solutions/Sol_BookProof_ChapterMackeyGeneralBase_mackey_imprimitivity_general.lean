-- Prove2me | solution 1 for BookProof.ChapterMackeyGeneralBase.mackey_imprimitivity_general
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-06T14:37:50.6682+00:00
-- url     : https://prove2.me/submissions/2b974100-170a-46c5-8871-8a23613b8f91

-- Generated from ChapterMackeyGeneralBase.lean — solution of BookProof.ChapterMackeyGeneralBase.mackey_imprimitivity_general
import Mathlib
import Definitions.Def_ChapterMackeyGeneralBase
import Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_add
import Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_smul
import Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_hasSum_norm_sq
import Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_mem_inducedSpace
import Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_injective
import Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_surjective
import Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_intertwines_U
import Theorems.Thm_BookProof_ChapterMackeyGeneralBase_mackeyMap_intertwines_pvm
open BookProof.ChapterMackeyGeneralBase



open scoped InnerProductSpace


open BookProof.ChapterOrthogonalSums

-- The platform target was published from an earlier text whose variable block
-- still carried `[Fintype X]` (the finite-base structure), so its `∀` opens that
-- instance binder.  It is unused by the statement, but `solution` must open the
-- SAME binders in the SAME order or the type check fails with `WA`.
variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (S : ImprimitivitySystem G X E)
variable (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

set_option maxHeartbeats 1000000 in
theorem solution [CompleteSpace E] [DecidableEq X]
    (S : ImprimitivitySystem G X E) (x₀ : X) (htrans : ∀ x : X, ∃ g : G, g • x₀ = x) :
    ∃ s : X → G, (∀ x, s x • x₀ = x) ∧
      (∀ ψ φ : E, mackeyMap S s (ψ + φ) = mackeyMap S s ψ + mackeyMap S s φ) ∧
      (∀ (a : ℂ) (ψ : E), mackeyMap S s (a • ψ) = a • mackeyMap S s ψ) ∧
      (∀ ψ : E, mackeyMap S s ψ ∈ InducedSpace S x₀) ∧
      (∀ ψ : E, HasSum (fun x => ‖mackeyMap S s ψ x‖ ^ 2) (‖ψ‖ ^ 2)) ∧
      Function.Injective (mackeyMap S s) ∧
      (∀ f ∈ InducedSpace S x₀, ∃ ψ : E, mackeyMap S s ψ = f) ∧
      (∀ (g : G) (ψ : E), mackeyMap S s (S.U g ψ) = inducedRep S s g (mackeyMap S s ψ)) ∧
      (∀ (y : X) (ψ : E), mackeyMap S s (S.p y ψ) = inducedPvm y (mackeyMap S s ψ)) := by

  classical
  refine ⟨fun x => (htrans x).choose, fun x => (htrans x).choose_spec, mackeyMap_add,
    mackeyMap_smul, fun ψ => mackeyMap_mem_inducedSpace (fun x => (htrans x).choose_spec) ψ,
    mackeyMap_hasSum_norm_sq, mackeyMap_injective,
    fun _ hf => mackeyMap_surjective (fun x => (htrans x).choose_spec) hf,
    fun g ψ => mackeyMap_intertwines_U (fun x => (htrans x).choose_spec) g ψ,
    mackeyMap_intertwines_pvm⟩
