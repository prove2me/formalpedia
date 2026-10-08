-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:09:05.617977+00:00
-- url     : https://prove2.me/submissions/bb33a9c5-1b1a-4c71-aaee-683df2d8c6dc

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_eigenvector
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa
open BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData





open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in
theorem solution {v : L.D} {p q dr : Fin 3 → ℝ} {c : ℝ}
    (hP : ∀ i, L.P i v = ((p i : ℝ) : ℂ) • v) (hQ : ∀ i, L.Q i v = ((q i : ℝ) : ℂ) • v)
    (hD : ∀ i, L.drive i v = ((dr i : ℝ) : ℂ) • v)
    (hC : L.constraintOp v = ((c : ℝ) : ℂ) • v) :
    L.hFull v = ((L.eigenvalue p q dr c : ℝ) : ℂ) • v := by

  have hPP : ∀ i, (L.P i).comp (L.P i) v = ((p i ^ 2 : ℝ) : ℂ) • v := by
    intro i
    simp only [LinearMap.comp_apply, map_smul, hP i, smul_smul]
    norm_num [pow_two]
  have hQQ : ∀ i, (L.Q i).comp (L.Q i) v = ((q i ^ 2 : ℝ) : ℂ) • v := by
    intro i
    simp only [LinearMap.comp_apply, map_smul, hQ i, smul_smul]
    norm_num [pow_two]
  simp only [hFull, kinetic, viscous, drift, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, hPP, hQQ, hD, hC, smul_smul, ← Finset.sum_smul, ← add_smul,
    eigenvalue]
  push_cast
  ring_nf
