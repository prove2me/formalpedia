-- Prove2me | solution 1 for BookProof.IrreversibleDynamics.dissipative_volume_image
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:18:25.138236+00:00
-- url     : https://prove2.me/submissions/7cdd2e7c-c45a-4a44-aba0-8a2b32bb5b73

-- Generated from ChapterIrreversibleDynamics.lean — solution of BookProof.IrreversibleDynamics.dissipative_volume_image
import Mathlib
import Definitions.Def_ChapterIrreversibleDynamics
open BookProof.IrreversibleDynamics




open MeasureTheory Function Set
open scoped ENNReal

set_option maxHeartbeats 1000000 in
theorem solution (A : Set ℝ) :
    volume (dissipative '' A) = volume A / 2 := by

  open Pointwise in
  have h : dissipative '' A = (2⁻¹ : ℝ) • A := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp [dissipative, smul_eq_mul]; ring⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp [dissipative, smul_eq_mul]; ring⟩
  rw [h, Measure.addHaar_smul]
  simp only [Module.finrank_self, pow_one, abs_inv, Nat.abs_ofNat, Nat.ofNat_pos,
    ENNReal.ofReal_inv_of_pos, ENNReal.ofReal_ofNat]
  rw [ENNReal.div_eq_inv_mul]
