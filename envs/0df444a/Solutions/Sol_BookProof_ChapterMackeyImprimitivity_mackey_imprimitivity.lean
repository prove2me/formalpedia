-- Prove2me | solution 1 for BookProof.ChapterMackeyImprimitivity.mackey_imprimitivity
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:34:39.670307+00:00
-- url     : https://prove2.me/submissions/a67b71d8-980c-4a57-8b0e-210775e272db
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterMackeyImprimitivity.lean — solution of BookProof.ChapterMackeyImprimitivity.mackey_imprimitivity
import Mathlib
import Definitions.Def_ChapterMackeyImprimitivity
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_add
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_smul
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_mem_inducedSpace
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_norm_sq
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_injective
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_surjective
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_intertwines_U
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackeyMap_intertwines_pvm
open BookProof.ChapterMackeyImprimitivity



open scoped InnerProductSpace
open Finset


variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable {G : Type*} [Group G] {X : Type*} [Fintype X] [MulAction G X]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (S : ImprimitivitySystem G X E)
variable (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
variable {S x₀ s}

set_option maxHeartbeats 1000000 in
theorem solution [DecidableEq X] (S : ImprimitivitySystem G X E) (x₀ : X) (s : X → G)
    (hs : ∀ x, s x • x₀ = x) :
    (∀ ψ φ : E, mackeyMap S s (ψ + φ) = mackeyMap S s ψ + mackeyMap S s φ) ∧
    (∀ (a : ℂ) (ψ : E), mackeyMap S s (a • ψ) = a • mackeyMap S s ψ) ∧
    (∀ ψ : E, mackeyMap S s ψ ∈ InducedSpace S x₀) ∧
    (∀ ψ : E, ∑ x : X, ‖mackeyMap S s ψ x‖ ^ 2 = ‖ψ‖ ^ 2) ∧
    Function.Injective (mackeyMap S s) ∧
    (∀ f ∈ InducedSpace S x₀, ∃ ψ : E, mackeyMap S s ψ = f) ∧
    (∀ (g : G) (ψ : E), mackeyMap S s (S.U g ψ) = inducedRep S s g (mackeyMap S s ψ)) ∧
    (∀ (y : X) (ψ : E), mackeyMap S s (S.p y ψ) = inducedPvm y (mackeyMap S s ψ)) :=
  ⟨mackeyMap_add, mackeyMap_smul, fun ψ => mackeyMap_mem_inducedSpace hs ψ,
      mackeyMap_norm_sq, mackeyMap_injective,
      fun _ hf => mackeyMap_surjective hs hf,
      fun g ψ => mackeyMap_intertwines_U hs g ψ, mackeyMap_intertwines_pvm⟩
