-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.core_ext
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-18T11:19:02.461901+00:00
-- url     : https://prove2.me/submissions/29dbed9a-c8a4-45c1-b11a-11b8501862cb

-- Generated from ChapterNavierStokesDifferentialL2.lean — solution of BookProof.NavierStokesFlow.DifferentialL2.core_ext
import Mathlib
import Definitions.Def_ChapterNavierStokesDifferentialL2
open BookProof.NavierStokesFlow.DifferentialL2




open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {M : Type*} [AddCommGroup M] [Module ℂ M]
    {F G : lpFiniteModes Vel →ₗ[ℂ] M} (h : ∀ b, F (coreState b) = G (coreState b)) : F = G := by

  refine LinearMap.ext fun x => ?_
  have hx : x ∈ Submodule.span ℂ (Set.range coreState) := by rw [span_coreState]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨b, rfl⟩ := hy; exact h b
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | smul a y _ hy => rw [map_smul, map_smul, hy]
