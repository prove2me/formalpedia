-- Prove2me | solution 1 for BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_relative_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T02:42:54.262106+00:00
-- url     : https://prove2.me/submissions/b9475a0e-2b01-4795-bcca-45e4e191d451

-- Generated from ChapterNavierStokesAffineFiberEsa.lean — solution of BookProof.NavierStokesFlow.AffineFiber.PairShift.pairH_relative_bound
import Mathlib
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Theorems.Thm_BookProof_NavierStokesFlow_AffineFiber_PairShift_pairH_apply
import Theorems.Thm_BookProof_NavierStokesFlow_ShiftHamiltonian_ShiftData_shiftH_relative_bound
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.AffineFiber.PairShift



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato HermiteFarisLavine ShiftHamiltonian
open BookProof.NavierStokesFlow.ShiftHamiltonian.ShiftData
open BookProof.NavierStokesFlow.AffineFiber

variable {ι : Type*}

variable {ι : Type*}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable (P : PairShift ι)

set_option maxHeartbeats 1000000 in
theorem solution (x : maxDom P.sym) :
    ‖(pairH P x : L2I ι)‖ ^ 2
      ≤ 2 * ‖(diagMax P.sym x : L2I ι)‖ ^ 2 + (32 * P.K ^ 2) * ‖(x : L2I ι)‖ ^ 2 := by

  have h₁ := ShiftData.shiftH_relative_bound P.fst x
  have h₂ := ShiftData.shiftH_relative_bound P.snd x
  have htri : ‖(pairH P x : L2I ι)‖
      ≤ ‖(ShiftData.shiftH P.fst x : L2I ι)‖ + ‖(ShiftData.shiftH P.snd x : L2I ι)‖ := by
    rw [pairH_apply]; exact norm_add_le _ _
  have hsq : ‖(pairH P x : L2I ι)‖ ^ 2
      ≤ 2 * ‖(ShiftData.shiftH P.fst x : L2I ι)‖ ^ 2
        + 2 * ‖(ShiftData.shiftH P.snd x : L2I ι)‖ ^ 2 := by
    nlinarith [norm_nonneg (pairH P x : L2I ι), norm_nonneg (ShiftData.shiftH P.fst x : L2I ι),
      norm_nonneg (ShiftData.shiftH P.snd x : L2I ι),
      sq_nonneg (‖(ShiftData.shiftH P.fst x : L2I ι)‖
        - ‖(ShiftData.shiftH P.snd x : L2I ι)‖)]
  have hK : P.fst.K = P.K := rfl
  have hK' : P.snd.K = P.K := rfl
  rw [hK] at h₁
  rw [hK'] at h₂
  have hsym : (diagMax P.fst.sym x : L2I ι) = (diagMax P.sym x : L2I ι) := rfl
  have hsym' : (diagMax P.snd.sym x : L2I ι) = (diagMax P.sym x : L2I ι) := rfl
  rw [hsym] at h₁
  rw [hsym'] at h₂
  linarith
