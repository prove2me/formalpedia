-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_commonEigenvectors
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T12:38:05.543554+00:00
-- url     : https://prove2.me/submissions/14ec6880-9b0e-46c3-a9f3-94f2bab66d1d

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_commonEigenvectors
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_hasZeroDeficiencyOn_of_total_eigenvectors
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianEsa_LagrangianFullData_hFull_eigenvector
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa
open BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData





open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in
theorem solution {I : Type*} (e : I → L.D)
    (p q dr : Fin 3 → I → ℝ) (c : I → ℝ)
    (hP : ∀ i a, L.P i (e a) = ((p i a : ℝ) : ℂ) • e a)
    (hQ : ∀ i a, L.Q i (e a) = ((q i a : ℝ) : ℂ) • e a)
    (hD : ∀ i a, L.drive i (e a) = ((dr i a : ℝ) : ℂ) • e a)
    (hC : ∀ a, L.constraintOp (e a) = ((c a : ℝ) : ℂ) • e a)
    (htotal : ∀ w : F, (∀ a, (inner ℂ ((e a : F)) w : ℂ) = 0) → w = 0) :
    HasZeroDeficiencyOn L.D L.hFull :=
  L.hasZeroDeficiencyOn_of_total_eigenvectors e
      (fun a => L.eigenvalue (fun i => p i a) (fun i => q i a) (fun i => dr i a) (c a))
      (fun a => L.hFull_eigenvector (fun i => hP i a) (fun i => hQ i a) (fun i => hD i a) (hC a))
      htotal
