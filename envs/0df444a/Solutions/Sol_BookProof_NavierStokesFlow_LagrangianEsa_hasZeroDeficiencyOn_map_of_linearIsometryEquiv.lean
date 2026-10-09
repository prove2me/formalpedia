-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.hasZeroDeficiencyOn_map_of_linearIsometryEquiv
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:45:58.336073+00:00
-- url     : https://prove2.me/submissions/4874f168-45e7-4225-9961-67dfa784c87d

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.hasZeroDeficiencyOn_map_of_linearIsometryEquiv
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
    (hmap : ∀ x : D, W (x : F) ∈ D')
    (hint : ∀ x : D, (H' ⟨W (x : F), hmap x⟩ : G) = W ((H x : F)))
    (h : HasZeroDeficiencyOn D H) : HasZeroDeficiencyOn D' H' := by

  have key : ∀ (c : ℂ), (∀ w : F, (∀ v : D, (inner ℂ (H v : F) w : ℂ)
      = inner ℂ (v : F) (c • w)) → w = 0) →
      ∀ w' : G, (∀ y : D', (inner ℂ (H' y : G) w' : ℂ) = inner ℂ (y : G) (c • w')) → w' = 0 := by
    intro c hc w' hw'
    have hW : W.symm w' = 0 := by
      refine hc (W.symm w') fun v => ?_
      have hleft : (inner ℂ (H v : F) (W.symm w') : ℂ) = inner ℂ (W ((H v : F))) w' := by
        rw [← W.inner_map_map ((H v : F)) (W.symm w')]
        simp
      have hright : (inner ℂ (v : F) (c • W.symm w') : ℂ) = inner ℂ (W (v : F)) (c • w') := by
        rw [inner_smul_right, inner_smul_right, ← W.inner_map_map (v : F) (W.symm w')]
        simp
      rw [hleft, hright, ← hint v]
      exact hw' ⟨W (v : F), hmap v⟩
    simpa using congrArg W hW
  refine ⟨key Complex.I h.1, fun w' hw' => ?_⟩
  refine key (-Complex.I) (fun w hw => h.2 w fun v => ?_) w' ?_
  · simpa using hw v
  · intro y
    simpa using hw' y
