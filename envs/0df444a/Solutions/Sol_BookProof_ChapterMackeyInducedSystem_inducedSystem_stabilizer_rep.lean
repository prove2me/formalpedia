-- Prove2me | solution 1 for BookProof.ChapterMackeyInducedSystem.inducedSystem_stabilizer_rep
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T02:40:13.813661+00:00
-- url     : https://prove2.me/submissions/ca255ce5-e927-4840-947d-7f307971d28b

-- Generated from ChapterMackeyInducedSystem.lean — solution of BookProof.ChapterMackeyInducedSystem.inducedSystem_stabilizer_rep
import Mathlib
import Definitions.Def_ChapterMackeyInducedSystem
import Theorems.Thm_BookProof_ChapterMackeyImprimitivity_cocycle_mem_stabilizer
import Definitions.Def_ChapterMackeyImprimitivity
open BookProof.ChapterMackeyInducedSystem



open scoped InnerProductSpace
open Finset


open BookProof.ChapterMackeyImprimitivity
open BookProof.ChapterMackeyImprimitivity.ImprimitivitySystem

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
    (hs : ∀ x, s x • x₀ = x) (hs0 : s x₀ = 1) (a : MulAction.stabilizer G x₀)
    (f : FieldSpace X K) :
    ((inducedSystem L s hs).U (a : G) f) x₀ = L a (f x₀) := by

  have hfix : (a : G)⁻¹ • x₀ = x₀ := by
    rw [inv_smul_eq_iff]
    exact a.2.symm
  have hc : cocycle s (a : G) x₀ = (a : G) := by
    rw [cocycle, hfix, hs0]
    group
  have hsub : (⟨cocycle s (a : G) x₀, cocycle_mem_stabilizer hs (a : G) x₀⟩ :
      MulAction.stabilizer G x₀) = a := Subtype.ext hc
  have hval : ((inducedSystem L s hs).U (a : G) f) x₀ =
      L ⟨cocycle s (a : G) x₀, cocycle_mem_stabilizer hs (a : G) x₀⟩
        (f ((a : G)⁻¹ • x₀)) := rfl
  rw [hval, hsub, hfix]
