-- Prove2me | solution 2 for CohnElkies.manuscriptPackingRoot_sub_deficit_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:31:51.6395+00:00
-- url     : https://prove2.me/submissions/3b06bd0d-b118-459a-9007-a8efd9c3d9d6

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter
open scoped Topology


theorem solution
    {d : ℕ} (hd : 0 < d) :
    (criticalPackingBase - manuscriptPackingDeficit d) ^ d ≤
      linearProgram d := by
  have hpos : ∀ q ∈ quotientSet d, 0 ≤ q := by
    rintro _ ⟨f, rfl⟩; exact (div_pos (admissible_zero_pos f) f.fourier_zero_pos).le
  have hLP : 0 ≤ linearProgram d := by
    unfold linearProgram
    exact mul_nonneg (div_pos (unitBallVolume_pos d) (by positivity)).le (Real.sInf_nonneg hpos)
  have hr : (linearProgram d ^ ((d:ℝ)⁻¹)) ^ d = linearProgram d :=
    Real.rpow_inv_natCast_pow hLP hd.ne'
  have hB : 0 ≤ criticalPackingBase := Real.sqrt_nonneg _
  unfold manuscriptPackingDeficit
  rcases le_total (linearProgram d ^ ((d:ℝ)⁻¹)) criticalPackingBase with h | h
  · rw [max_eq_right (by linarith), sub_sub_cancel, hr]
  · rw [max_eq_left (by linarith), sub_zero]
    calc criticalPackingBase ^ d ≤ (linearProgram d ^ ((d:ℝ)⁻¹)) ^ d := pow_le_pow_left₀ hB h d
      _ = _ := hr

