-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineFiber.affH_ne_zero_of_pos_shear
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:41.57575+00:00
-- url     : https://prove2.me/submissions/3205d622-56a2-4b90-94c7-7167fc6dfa0c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — solution of BookProof.NavierStokesFlow.AffineFiber.affH_ne_zero_of_pos_shear
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_affH_coord_succ
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian

variable {ι : Type*}

variable {ι : Type*}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable (P : PairShift ι)

set_option maxHeartbeats 1000000 in

theorem solution {κ c : ℝ} (hκ : 0 ≤ κ) (hc : 0 < c) :
    affH hκ hc.le (basisState κ c 0) ≠ 0 := by
  intro h0
  have hcoord := affH_coord_succ hκ hc.le 0
  rw [h0] at hcoord
  simp only [lp.coeFn_zero, Pi.zero_apply] at hcoord
  have hshear : shear c 0 ≠ 0 := by
    have h2 : (0 : ℝ) < Real.sqrt 2 := by rw [Real.sqrt_pos]; norm_num
    have h1 : (0 : ℝ) < Real.sqrt (((0 : ℕ) : ℝ) + 1) := by rw [Real.sqrt_pos]; norm_num
    unfold shear
    positivity
  have hz : ((shear c 0 : ℝ) : ℂ) = 0 := by
    have h := hcoord.symm
    field_simp at h
    simpa using h
  exact hshear (by exact_mod_cast hz)
