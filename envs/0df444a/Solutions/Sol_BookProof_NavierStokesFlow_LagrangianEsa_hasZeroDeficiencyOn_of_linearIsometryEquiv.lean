-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.hasZeroDeficiencyOn_of_linearIsometryEquiv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:16:05.17599+00:00
-- url     : https://prove2.me/submissions/0e93d673-0b08-46d9-a149-49ae413935bf

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.hasZeroDeficiencyOn_of_linearIsometryEquiv
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa





open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

set_option maxHeartbeats 1000000 in
theorem solution (W : F ≃ₗᵢ[ℂ] G) {D : Submodule ℂ F}
    {D' : Submodule ℂ G} {H : D →ₗ[ℂ] D} {H' : D' →ₗ[ℂ] D'}
    (hmap : ∀ x : D, W (x : F) ∈ D') (hsurj : ∀ y : D', ∃ x : D, W (x : F) = (y : G))
    (hint : ∀ x : D, (H' ⟨W (x : F), hmap x⟩ : G) = W ((H x : F)))
    (h : HasZeroDeficiencyOn D' H') : HasZeroDeficiencyOn D H := by

  have key : ∀ (c : ℂ), (∀ w' : G, (∀ y : D', (inner ℂ (H' y : G) w' : ℂ)
      = inner ℂ (y : G) (c • w')) → w' = 0) →
      ∀ w : F, (∀ v : D, (inner ℂ (H v : F) w : ℂ) = inner ℂ (v : F) (c • w)) → w = 0 := by
    intro c hc w hw
    have hW : W w = 0 := by
      refine hc (W w) fun y => ?_
      obtain ⟨x, hx⟩ := hsurj y
      have hHy : (H' y : G) = W ((H x : F)) := by
        have hxy : (⟨W (x : F), hmap x⟩ : D') = y := Subtype.ext hx
        rw [← hxy, hint x]
      rw [hHy, ← hx, W.inner_map_map, hw x, inner_smul_right, inner_smul_right,
        W.inner_map_map]
    have := congrArg W.symm hW
    simpa using this
  refine ⟨key Complex.I h.1, fun w hw => ?_⟩
  refine key (-Complex.I) (fun w' hw' => h.2 w' fun y => ?_) w ?_
  · simpa using hw' y
  · intro v
    simpa using hw v
