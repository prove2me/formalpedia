-- Prove2me | solution 1 for BookProof.HashimotoShiftInvert.IsShiftInvert.dom_eq_range
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-02T01:43:37.149307+00:00
-- url     : https://prove2.me/submissions/4ebc8aeb-6bc2-4a8f-bf08-7d4e5c0931e2

-- Generated from ChapterHashimotoShiftInvert.lean — solution of BookProof.HashimotoShiftInvert.IsShiftInvert.dom_eq_range
import Mathlib
import Definitions.Def_ChapterHashimotoShiftInvert
import Theorems.Thm_BookProof_HashimotoShiftInvert_IsShiftInvert_mem
open BookProof.HashimotoShiftInvert




open BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.YangMillsFriedrichsLimit
open BookProof.HermiteGalerkin
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {Dom : Submodule ℂ F}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {Dom : Submodule ℂ F}

set_option maxHeartbeats 1000000 in
theorem solution {A : Dom →ₗ[ℂ] F} {γ : ℝ} {R : F →L[ℂ] F}
    (h : IsShiftInvert A γ R) : Dom = LinearMap.range (R : F →ₗ[ℂ] F) := by

  apply le_antisymm
  · intro x hx
    exact ⟨shiftMap A γ ⟨x, hx⟩, h.1 ⟨x, hx⟩⟩
  · rintro _ ⟨u, rfl⟩
    exact h.mem u
