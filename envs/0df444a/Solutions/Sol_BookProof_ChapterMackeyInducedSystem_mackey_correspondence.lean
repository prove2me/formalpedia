-- Prove2me | solution 1 for BookProof.ChapterMackeyInducedSystem.mackey_correspondence
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-12T12:01:15.083899+00:00
-- url     : https://prove2.me/submissions/93066491-1114-4ae6-9e82-ba71f2a61d6a

-- Generated from ChapterMackeyInducedSystem.lean — solution of BookProof.ChapterMackeyInducedSystem.mackey_correspondence
import Mathlib
import Definitions.Def_ChapterMackeyInducedSystem
import Theorems.Thm_BookProof_ChapterMackeyInducedSystem_inducedSystem_fibre
import Theorems.Thm_BookProof_ChapterMackeyInducedSystem_inducedSystem_stabilizer_rep
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_mackey_imprimitivity
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyInducedSystem



open scoped InnerProductSpace
open Finset


open BookProof.ChapterMackeyImprimitivity

variable {G : Type*} [Group G] {X : Type*} [Fintype X] [DecidableEq X] [MulAction G X]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable {x₀ : X}

variable {G : Type*} [Group G] {X : Type*} [Fintype X] [DecidableEq X] [MulAction G X]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
variable {x₀ : X}
variable {L : MulAction.stabilizer G x₀ →* (K ≃ₗᵢ[ℂ] K)} {s : X → G}
variable (L s)
variable {L s}
variable (X K) in

set_option maxHeartbeats 1000000 in
theorem solution (L : MulAction.stabilizer G x₀ →* (K ≃ₗᵢ[ℂ] K)) (s : X → G)
    (hs : ∀ x, s x • x₀ = x) (hs0 : s x₀ = 1) :
    (∀ (a : MulAction.stabilizer G x₀) (f : FieldSpace X K),
        ((inducedSystem L s hs).U (a : G) f) x₀ = L a (f x₀)) ∧
    (∀ f : FieldSpace X K, (inducedSystem L s hs).p x₀ f = f ↔ ∀ x, x ≠ x₀ → f x = 0) ∧
    ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
      (S : ImprimitivitySystem G X E),
      (∀ ψ φ : E, mackeyMap S s (ψ + φ) = mackeyMap S s ψ + mackeyMap S s φ) ∧
      (∀ ψ : E, ∑ x : X, ‖mackeyMap S s ψ x‖ ^ 2 = ‖ψ‖ ^ 2) ∧
      Function.Injective (mackeyMap S s) ∧
      (∀ f ∈ InducedSpace S x₀, ∃ ψ : E, mackeyMap S s ψ = f) ∧
      (∀ (g : G) (ψ : E), mackeyMap S s (S.U g ψ) = inducedRep S s g (mackeyMap S s ψ)) ∧
      (∀ (y : X) (ψ : E), mackeyMap S s (S.p y ψ) = inducedPvm y (mackeyMap S s ψ)) := by

  -- The platform statement was published with `variable (X K) in` in its
  -- preamble, so `inducedSystem_stabilizer_rep` / `inducedSystem_fibre` take
  -- X and K as EXPLICIT leading arguments; passing L positionally put it in
  -- the X slot (`Application type mismatch: ... expected Type`).
  refine ⟨inducedSystem_stabilizer_rep X K L s hs hs0,
    inducedSystem_fibre X K L s hs, ?_⟩
  intro E _ _ S
  obtain ⟨h1, _, _, h4, h5, h6, h7, h8⟩ := mackey_imprimitivity S x₀ s hs
  exact ⟨h1, h4, h5, h6, h7, h8⟩
