-- Prove2me | solution 1 for BookProof.RitzMinMax.exists_unit_mem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-10T10:45:18.930727+00:00
-- url     : https://prove2.me/submissions/b50c475d-78e2-4ab6-9dd9-46a2f3846766

-- Generated from ChapterSirkRitzMinMax.lean — solution of BookProof.RitzMinMax.exists_unit_mem
import Mathlib
import Definitions.Def_ChapterSirkRitzMinMax
open BookProof.RitzMinMax










noncomputable section


open BookProof.HermiteGalerkin BookProof.ChapterSirkRitzSpectrum
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution (S : Submodule ℂ F) (hS : 0 < Module.finrank ℂ S) :
    ∃ x : F, x ∈ S ∧ ‖x‖ = 1 := by

  have hne : S ≠ ⊥ := by
    intro h
    rw [h] at hS
    simp at hS
  obtain ⟨y, hy, hy0⟩ := S.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨‖y‖⁻¹ • y, S.smul_mem _ hy, ?_⟩
  rw [norm_smul]
  simp [norm_ne_zero_iff.mpr hy0]
