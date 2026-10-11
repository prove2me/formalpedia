-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianEsa.jacobiLagData_hFull
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:19:54.4852+00:00
-- url     : https://prove2.me/submissions/5fd23854-2a14-4731-abed-af1be25a41aa

-- Generated from ChapterNavierStokesLagrangianEsa.lean — solution of BookProof.NavierStokesFlow.LagrangianEsa.jacobiLagData_hFull
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianEsa





open FullEsa
open BookProof.BRSTNilpotent
open BookProof.ChapterF7
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)
variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

set_option maxHeartbeats 1000000 in

theorem solution : jacobiLagData.hFull = jacobiOp := by
  have hP : ∀ i : Fin 3, jacobiLagData.P i = 0 := fun _ => rfl
  have hQ : ∀ i : Fin 3, jacobiLagData.Q i = 0 := fun _ => rfl
  have hC : jacobiLagData.constraintOp = 0 := rfl
  have hd0 : jacobiLagData.drive 0 = jacobiOp := by
    change (if (0 : Fin 3) = 0 then jacobiOp else 0) = jacobiOp
    rw [if_pos rfl]
  have hd1 : jacobiLagData.drive 1 = 0 := by
    change (if (1 : Fin 3) = 0 then jacobiOp else 0) = 0
    rw [if_neg (by decide)]
  have hd2 : jacobiLagData.drive 2 = 0 := by
    change (if (2 : Fin 3) = 0 then jacobiOp else 0) = 0
    rw [if_neg (by decide)]
  have hf0 : jacobiLagData.force 0 = 1 := by
    change (if (0 : Fin 3) = 0 then (1 : ℝ) else 0) = 1
    rw [if_pos rfl]
  have hf1 : jacobiLagData.force 1 = 0 := by
    change (if (1 : Fin 3) = 0 then (1 : ℝ) else 0) = 0
    rw [if_neg (by decide)]
  have hf2 : jacobiLagData.force 2 = 0 := by
    change (if (2 : Fin 3) = 0 then (1 : ℝ) else 0) = 0
    rw [if_neg (by decide)]
  have hkin : jacobiLagData.kinetic = 0 := by
    simp [LagrangianFullData.kinetic, hP]
  have hvis : jacobiLagData.viscous = 0 := by
    simp [LagrangianFullData.viscous, hQ]
  have hdrift : jacobiLagData.drift = jacobiOp := by
    simp only [LagrangianFullData.drift, Fin.sum_univ_three]
    simp [hd1, hd2, hf0, hf1, hf2]
    rw [hd0]
    all_goals first | rfl | exact one_smul _ _
  simp [LagrangianFullData.hFull, hkin, hvis, hdrift, hC]
  all_goals exact zero_add _
