-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.diagLagData_hFull
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T04:47:14.240377+00:00
-- url     : https://prove2.me/submissions/90f5d5ca-bcc9-4782-aa17-b84bdf4819cd

import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
-- Generated from ChapterNavierStokesLagrangianEsa.lean — theorem BookProof.NavierStokesFlow.LagrangianEsa.diagLagData_hFull
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.BRSTNilpotent
open BookProof.ChapterF7
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa




open FullEsa

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]
theorem h43_L2N_add_apply (f g : BookProof.NavierStokesFlow.LpNat.L2N) (n : ℕ) :
    ((f + g : BookProof.NavierStokesFlow.LpNat.L2N) : ℕ → ℂ) n = (f : ℕ → ℂ) n + (g : ℕ → ℂ) n := rfl

theorem h43_L2N_smul_apply (c : ℂ) (f : BookProof.NavierStokesFlow.LpNat.L2N) (n : ℕ) :
    ((c • f : BookProof.NavierStokesFlow.LpNat.L2N) : ℕ → ℂ) n = c * (f : ℕ → ℂ) n := rfl

theorem h43_diagOp_zd (c : ℕ → ℝ) :
    HasZeroDeficiencyOn (lpFiniteModes ℕ) (BookProof.NavierStokesFlow.DiagonalEsa.diagOp c) := by
  have key : ∀ z : ℂ, z.im ≠ 0 → ∀ w : BookProof.NavierStokesFlow.LpNat.L2N,
      (∀ v : lpFiniteModes ℕ, (inner ℂ ((BookProof.NavierStokesFlow.DiagonalEsa.diagOp c v : lpFiniteModes ℕ) : BookProof.NavierStokesFlow.LpNat.L2N) w : ℂ)
        = inner ℂ ((v : lpFiniteModes ℕ) : BookProof.NavierStokesFlow.LpNat.L2N) (z • w)) → w = 0 := by
    intro z hz w hw
    ext n
    have h := hw (BookProof.NavierStokesFlow.DiagonalEsa.basis n)
    have e1 : ((BookProof.NavierStokesFlow.DiagonalEsa.diagOp c (BookProof.NavierStokesFlow.DiagonalEsa.basis n) : lpFiniteModes ℕ) : BookProof.NavierStokesFlow.LpNat.L2N)
        = lp.single 2 n ((c n : ℂ)) := by
      apply lp.ext; funext k
      show (c k : ℂ) * (lp.single 2 n (1 : ℂ) : ℕ → ℂ) k = (lp.single 2 n ((c n : ℂ)) : ℕ → ℂ) k
      rw [lp.single_apply, lp.single_apply, Pi.single_apply, Pi.single_apply]
      split_ifs with hk
      · subst hk; ring
      · ring
    rw [e1] at h
    change inner ℂ (lp.single 2 n ((c n : ℂ))) w = inner ℂ (lp.single 2 n (1 : ℂ)) (z • w) at h
    rw [lp.inner_single_left, lp.inner_single_left] at h
    simp only [RCLike.inner_apply, Complex.conj_ofReal, map_one, one_mul, h43_L2N_smul_apply] at h
    have h2 : ((c n : ℂ) - z) * (w : ℕ → ℂ) n = 0 := by linear_combination h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exfalso; apply hz
      have := congrArg Complex.im h3
      simpa using this.symm
    · simpa using h3
  refine ⟨key Complex.I (by simp), ?_⟩
  intro w hw
  exact key (-Complex.I) (by simp) w (fun v => by rw [hw v, neg_smul])

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

theorem h43_diagLag_zd (p q dr : Fin 3 → ℕ → ℝ) (c : ℕ → ℝ) (fr : Fin 3 → ℝ)
    {nu : ℝ} (hnu : 0 ≤ nu) :
    HasZeroDeficiencyOn (diagLagData p q dr c fr hnu).D (diagLagData p q dr c fr hnu).hFull := by
  rw [h43_diagLag_eq]; exact h43_diagOp_zd _

theorem solution (p q dr : Fin 3 → ℕ → ℝ) (c : ℕ → ℝ) (fr : Fin 3 → ℝ)
    {nu : ℝ} (hnu : 0 ≤ nu) :
    HasZeroDeficiencyOn (diagLagData p q dr c fr hnu).D (diagLagData p q dr c fr hnu).hFull := by
  exact h43_diagLag_zd p q dr c fr hnu

