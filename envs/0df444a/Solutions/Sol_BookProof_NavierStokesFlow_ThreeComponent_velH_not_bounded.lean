-- Prove2me | solution 1 for BookProof.NavierStokesFlow.ThreeComponent.velH_not_bounded
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:20:46.109399+00:00
-- url     : https://prove2.me/submissions/668af800-3f91-435a-b669-b9d58ad22eaf

-- Generated from ChapterNavierStokesThreeComponent.lean — solution of BookProof.NavierStokesFlow.ThreeComponent.velH_not_bounded
import Mathlib
import Definitions.Def_ChapterNavierStokesThreeComponent
import Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_norm_velState
import Theorems.Thm_BookProof_NavierStokesFlow_ThreeComponent_velH_coord_diag_tower
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterNavierStokesShiftHamiltonian
import Definitions.Def_ChapterNavierStokesSignedShift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.ThreeComponent
















open scoped ENNReal



open BookProof.NavierStokesFlow.LpNat BookProof.FarisLavine BookProof.NavierStokesFlow.IkebeKato BookProof.NavierStokesFlow.ShiftHamiltonian BookProof.NavierStokesFlow.SignedShift





































variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

set_option maxHeartbeats 1000000 in
theorem solution (hA : A 0 0 ≠ 0) (C : ℝ) :
    ∃ β : Vel, ‖(velState A c β : L2I Vel)‖ = 1
      ∧ C < ‖(velH A c (velState A c β) : L2I Vel)‖ := by

  have hpos : 0 < |A 0 0| := abs_pos.mpr hA
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * (|C| + 1) / |A 0 0|)
  refine ⟨![n + 1, 0, 0], norm_velState A c _, ?_⟩
  have hb : ‖((velH A c (velState A c ![n + 1, 0, 0]) : L2I Vel) : Vel → ℂ) ![n + 3, 0, 0]‖
      ≤ ‖(velH A c (velState A c ![n + 1, 0, 0]) : L2I Vel)‖ :=
    lp.norm_apply_le_norm (by norm_num) _ _
  rw [velH_coord_diag_tower] at hb
  have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsq : ((n : ℝ) + 2) ≤ Real.sqrt (((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2)) := by
    have h := Real.sqrt_le_sqrt
      (show ((n : ℝ) + 2) ^ 2 ≤ ((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2) by nlinarith)
    rwa [Real.sqrt_sq (by linarith)] at h
  have hnorm : ‖Complex.I * ((A 0 0 / 2 * Real.sqrt (((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2)) :
        ℝ) : ℂ)‖
      = |A 0 0| / 2 * Real.sqrt (((n : ℝ) + 1 + 1) * ((n : ℝ) + 1 + 2)) := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    norm_num
  rw [hnorm] at hb
  have hmul : 2 * (|C| + 1) < |A 0 0| * (n : ℝ) := by
    rw [div_lt_iff₀ hpos] at hn
    linarith
  have hC : C ≤ |C| := le_abs_self C
  nlinarith [hsq, hpos.le]
