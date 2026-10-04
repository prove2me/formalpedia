-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.shiftMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-02T14:24:49.578735+00:00
-- url     : https://prove2.me/submissions/2c6aee54-2e55-4f61-b5ac-fff31b61a350

-- Generated from ChapterHashimotoShiftInvert.lean — solution of BookProof.HashimotoShiftInvert.shiftMap_injective
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Theorems.Thm_BookProof_HashimotoShiftInvert_norm_shiftMap_ge
open BookProof.HashimotoShiftInvert




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {A : Dom →ₗ[ℂ] F} (hpos : ∀ x : Dom, 0 ≤ quadForm A x)
    {γ : ℝ} (hγ : 0 < γ) : Function.Injective (shiftMap A γ) := by

  intro x y hxy
  have h : γ * ‖((x - y : Dom) : F)‖ ≤ ‖shiftMap A γ (x - y)‖ := norm_shiftMap_ge hpos _
  rw [map_sub, hxy, sub_self, norm_zero] at h
  have hx : ‖((x - y : Dom) : F)‖ = 0 := le_antisymm (by nlinarith) (norm_nonneg _)
  have : ((x - y : Dom) : F) = 0 := by simpa using hx
  have hz : x - y = 0 := Subtype.ext (by simpa using this)
  exact sub_eq_zero.mp hz
