-- Prove2me | solution 1 for BookProof.ChapterBornMeasure.lintegral_bornDensity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:31:25.688981+00:00
-- url     : https://prove2.me/submissions/fa8e57ab-5bf4-4de4-9f84-14cdcd80d53b

-- Generated from ChapterBornMeasure.lean — solution of BookProof.ChapterBornMeasure.lintegral_bornDensity
import Mathlib
import Definitions.Def_ChapterBornMeasure
open BookProof.ChapterBornMeasure



open MeasureTheory
open scoped ENNReal


variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution (psi : Lp ℂ 2 μ) (hpsi : ‖psi‖ = 1) :
    ∫⁻ x, ‖(psi : α → ℂ) x‖ₑ ^ 2 ∂μ = 1 := by

  have h := MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) (p := 2)
    (f := fun x => (psi : α → ℂ) x) (by norm_num) (by norm_num)
  have hne : eLpNorm (psi : α → ℂ) 2 μ ≠ ∞ := Lp.eLpNorm_ne_top psi
  have hnorm : (eLpNorm (psi : α → ℂ) 2 μ).toReal = 1 := by rw [← Lp.norm_def]; exact hpsi
  have heq : eLpNorm (psi : α → ℂ) 2 μ = 1 := by rwa [← ENNReal.toReal_eq_one_iff]
  rw [heq] at h
  norm_num at h
  have h2 := congrArg (fun x : ℝ≥0∞ => x ^ (2 : ℝ)) h
  simp only [ENNReal.one_rpow, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul] at h2
  norm_num at h2
  exact h2.symm
