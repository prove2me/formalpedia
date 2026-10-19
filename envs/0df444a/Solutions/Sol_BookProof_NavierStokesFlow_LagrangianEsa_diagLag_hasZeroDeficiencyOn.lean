-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.diagLag_hasZeroDeficiencyOn
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:47:37.264585+00:00
-- url     : https://prove2.me/submissions/f6ac27a2-a847-4547-8c97-022baaf8f8ea

import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.diagLag_hasZeroDeficiencyOn
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
theorem h43_diagOp_add (a b : ℕ → ℝ) :
    BookProof.NavierStokesFlow.DiagonalEsa.diagOp a + BookProof.NavierStokesFlow.DiagonalEsa.diagOp b
      = BookProof.NavierStokesFlow.DiagonalEsa.diagOp (fun n => a n + b n) := by
  apply LinearMap.ext; intro f; apply Subtype.ext; apply lp.ext; funext n
  show (a n : ℂ) * (f : ℕ → ℂ) n + (b n : ℂ) * (f : ℕ → ℂ) n = ((a n + b n : ℝ) : ℂ) * (f : ℕ → ℂ) n
  push_cast; ring

theorem h43_diagOp_smul (r : ℝ) (a : ℕ → ℝ) :
    (r : ℂ) • BookProof.NavierStokesFlow.DiagonalEsa.diagOp a
      = BookProof.NavierStokesFlow.DiagonalEsa.diagOp (fun n => r * a n) := by
  apply LinearMap.ext; intro f; apply Subtype.ext; apply lp.ext; funext n
  show (r : ℂ) * ((a n : ℂ) * (f : ℕ → ℂ) n) = ((r * a n : ℝ) : ℂ) * (f : ℕ → ℂ) n
  push_cast; ring

theorem h43_diagLag_eq (p q dr : Fin 3 → ℕ → ℝ) (c : ℕ → ℝ) (fr : Fin 3 → ℝ)
    {nu : ℝ} (hnu : 0 ≤ nu) :
    (diagLagData p q dr c fr hnu).hFull = BookProof.NavierStokesFlow.DiagonalEsa.diagOp (diagLagSymbol p q dr c fr nu) := by
  dsimp only [LagrangianFullData.hFull, LagrangianFullData.kinetic, LagrangianFullData.viscous,
    LagrangianFullData.drift, diagLagData]
  simp only [Fin.sum_univ_three, FullEsa.diagOp_comp, h43_diagOp_add, h43_diagOp_smul]
  congr 1; funext n
  simp only [diagLagSymbol, Fin.sum_univ_three]

theorem h43_diagLagUnb :
    diagLagUnbounded.hFull = BookProof.NavierStokesFlow.DiagonalEsa.diagOp (fun n => (1 / 2) * (n : ℝ) ^ 2) := by
  unfold diagLagUnbounded
  rw [h43_diagLag_eq]
  congr 1; funext n
  simp [diagLagSymbol, Fin.sum_univ_three]; ring

theorem solution :
    diagLagUnbounded.hFull = diagOp (fun n => (1 / 2) * (n : ℝ) ^ 2) := by
  exact h43_diagLagUnb

