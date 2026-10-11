-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FullEsa.jacobiFullData_hamiltonian
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:19:48.092532+00:00
-- url     : https://prove2.me/submissions/b6ef15a7-8ed0-4645-93a1-d63b5e9f1452

-- Generated from ChapterNavierStokesFullEsa.lean — solution of BookProof.NavierStokesFlow.FullEsa.jacobiFullData_hamiltonian
import Mathlib
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FullEsa



open scoped ENNReal
open BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.DiagonalEsa
open BookProof.NavierStokesFlow.JacobiDeficiency
open BookProof.NavierStokesFlow.LpNat

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {D : Submodule ℂ F}
variable (d : NSFullData F)

set_option maxHeartbeats 1000000 in

theorem solution : jacobiFullData.hamiltonian = jacobiOp := by
  have hvel : ∀ j : Fin 3, jacobiFullData.velocity j = 0 := by
    intro j
    have h : nsVelIdx j ≠ nsLapIdx 0 := by
      fin_cases j <;> decide
    exact jacobiMode_of_ne h
  have hlap0 : jacobiFullData.lapVelocity 0 = ((-1 / 2 : ℝ) : ℂ) • LinearMap.id :=
    jacobiMode_lap
  have hlapne : ∀ i : Fin 3, i ≠ 0 → jacobiFullData.lapVelocity i = 0 := by
    intro i hi
    refine jacobiMode_of_ne ?_
    fin_cases i
    · exact absurd rfl hi
    · decide
    · decide
  have hsum : ∀ i : Fin 3,
      (∑ j : Fin 3, (jacobiFullData.velocity j).comp (jacobiFullData.gradVelocity i j)) = 0 := by
    intro i
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hvel j, LinearMap.zero_comp]
  have hnu : ((jacobiFullData.nu : ℝ) : ℂ) = 1 := by
    change ((1 : ℝ) : ℂ) = 1
    norm_num
  have hadv0 : jacobiFullData.advection 0 = ((1 / 2 : ℝ) : ℂ) • LinearMap.id := by
    rw [NSFullData.advection, hsum 0, hlap0, hnu, zero_sub, smul_smul, one_mul]
    norm_num
  have hadvne : ∀ i : Fin 3, i ≠ 0 → jacobiFullData.advection i = 0 := by
    intro i hi
    rw [NSFullData.advection, hsum i, hlapne i hi, smul_zero, sub_zero]
  have hmom0 : jacobiFullData.mom 0 = jacobiOp := jacobiMom_zero
  have hmomne : ∀ i : Fin 3, i ≠ 0 → jacobiFullData.mom i = 0 := fun i hi => jacobiMom_of_ne hi
  rw [NSFullData.hamiltonian, Fin.sum_univ_three, hadv0,
    hadvne 1 (by decide), hadvne 2 (by decide), hmomne 1 (by decide), hmomne 2 (by decide)]
  simp only [LinearMap.comp_zero, add_zero,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_id, LinearMap.id_comp]
  rw [← add_smul]
  have hhalf : ((1 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) = 1 := by norm_num
  rw [hhalf, one_smul]
  exact hmom0
