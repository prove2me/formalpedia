-- Prove2me | solution 1 for BookProof.SpectralGapStability.exists_gapAt_of_notMem_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T15:03:24.408069+00:00
-- url     : https://prove2.me/submissions/6c113299-d815-4018-8314-91f28b2076b5

-- Generated from ChapterSpectralGapStability.lean — solution of BookProof.SpectralGapStability.exists_gapAt_of_notMem_spectrum
import Mathlib
import Definitions.Def_ChapterSpectralGapStability
open BookProof.SpectralGapStability



noncomputable section


open scoped InnerProductSpace
open Filter Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

set_option maxHeartbeats 1000000 in
theorem solution {A : F →L[ℂ] F} {lam : ℝ}
    (h : (lam : ℂ) ∉ spectrum ℂ A) : ∃ d > 0, GapAt A lam d := by

  rw [spectrum.mem_iff] at h
  push_neg at h
  have halg : (algebraMap ℂ (F →L[ℂ] F)) (lam : ℂ) - A = -(A - (lam : ℂ) • (1 : F →L[ℂ] F)) := by
    rw [Algebra.algebraMap_eq_smul_one]; abel
  rw [halg] at h
  have hBunit : IsUnit (A - (lam : ℂ) • (1 : F →L[ℂ] F)) := (IsUnit.neg_iff _).mp h
  set B : F →L[ℂ] F := A - (lam : ℂ) • (1 : F →L[ℂ] F) with hBdef
  set V : F →L[ℂ] F := ↑(hBunit.unit⁻¹) with hV
  have hVB : ∀ x : F, V (B x) = x := by
    intro x
    have hmul : V * B = 1 := by
      rw [hV]
      simp
    calc V (B x) = (V * B) x := rfl
      _ = (1 : F →L[ℂ] F) x := by rw [hmul]
      _ = x := rfl
  refine ⟨1 / (‖V‖ + 1), by positivity, ?_⟩
  intro x
  have hBx : B x = A x - (lam : ℂ) • x := by simp [hBdef]
  have h1 : ‖x‖ ≤ ‖V‖ * ‖B x‖ := by
    calc ‖x‖ = ‖V (B x)‖ := by rw [hVB x]
      _ ≤ ‖V‖ * ‖B x‖ := V.le_opNorm _
  have h2 : ‖x‖ ≤ (‖V‖ + 1) * ‖B x‖ := by nlinarith [norm_nonneg (B x), norm_nonneg V]
  rw [← hBx, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  linarith [h2]
