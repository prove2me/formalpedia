-- Prove2me | solution 1 for BookProof.ChapterMackeyInducedSystem.inducedSystem_fibre
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T02:38:40.710996+00:00
-- url     : https://prove2.me/submissions/94ee90bd-bdef-4be3-a7b5-1010f27a1455

-- Generated from ChapterMackeyInducedSystem.lean — solution of BookProof.ChapterMackeyInducedSystem.inducedSystem_fibre
import Mathlib
import Definitions.Def_ChapterMackeyInducedSystem
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
    (hs : ∀ x, s x • x₀ = x) (f : FieldSpace X K) :
    (inducedSystem L s hs).p x₀ f = f ↔ ∀ x, x ≠ x₀ → f x = 0 := by

  constructor
  · intro hfix x hx
    have hco : ((inducedSystem L s hs).p x₀ f) x = f x :=
      congrFun (congrArg WithLp.ofLp hfix) x
    rw [show ((inducedSystem L s hs).p x₀ f) x = if x = x₀ then f x else 0 from rfl,
      if_neg hx] at hco
    exact hco.symm
  · intro hsupp
    ext x
    rw [show ((inducedSystem L s hs).p x₀ f) x = if x = x₀ then f x else 0 from rfl]
    by_cases hx : x = x₀
    · simp [hx]
    · simp [hx, hsupp x hx]
