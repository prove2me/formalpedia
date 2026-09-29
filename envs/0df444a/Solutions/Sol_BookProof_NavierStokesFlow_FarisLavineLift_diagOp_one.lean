-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.diagOp_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T00:11:57.623828+00:00
-- url     : https://prove2.me/submissions/8c52e333-4a5b-48ca-a9b7-c3aa5e7ffc6a

-- Generated from ChapterNavierStokesFarisLavineLift.lean — solution of BookProof.NavierStokesFlow.FarisLavineLift.diagOp_one
import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift











open FullEsa



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]






variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]



variable {d : ℕ} (c : ComparisonData F d)











open LpNat DiagonalEsa

set_option maxHeartbeats 1000000 in
theorem solution :
    (LinearMap.id : lpFiniteModes ℕ →ₗ[ℂ] lpFiniteModes ℕ) = diagOp (fun _ => 1) := by

  refine LinearMap.ext fun f => Subtype.ext (lp.ext ?_)
  funext n
  simp [diagOp, diagFun]
