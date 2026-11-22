-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_original_time_mark_negative_bin_integral_error_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:06:58.769921+00:00
-- url     : https://prove2.me/submissions/f9b405d8-76ae-4887-a1fd-c5f0fd6d5371

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0) (i : ℕ)
    (hFin : μ (Ioc (0 : ℝ≥0) T ×ˢ
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))) < ⊤) :
    |∫ p in Ioc (0 : ℝ≥0) T ×ˢ
      Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2))),
      p.2 + 1 / ((i : ℝ) + 1) ∂μ| ≤
    (1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))) *
      μ.real (Ioc (0 : ℝ≥0) T ×ˢ
        Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))) := by
  classical
  let B : Set ℝ :=
    Ioc (-(1 / ((i : ℝ) + 1))) (-(1 / ((i : ℝ) + 2)))
  let R : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) T ×ˢ B
  let δ : ℝ := 1 / (((i : ℝ) + 1) * ((i : ℝ) + 2))
  have hWidth :
      (1 / ((i : ℝ) + 1)) - (1 / ((i : ℝ) + 2)) = δ := by
    dsimp [δ]
    field_simp
    ring
  have hBound : ∀ p ∈ R,
      ‖p.2 + 1 / ((i : ℝ) + 1)‖ ≤ δ := by
    intro p hp
    have hz := hp.2
    have hNonneg : 0 ≤ p.2 + 1 / ((i : ℝ) + 1) := by
      have hLeft := hz.1
      linarith
    have hLe : p.2 + 1 / ((i : ℝ) + 1) ≤ δ := by
      rw [← hWidth]
      have hRight := hz.2
      linarith
    calc
      ‖p.2 + 1 / ((i : ℝ) + 1)‖ =
          |p.2 + 1 / ((i : ℝ) + 1)| := Real.norm_eq_abs _
      _ = p.2 + 1 / ((i : ℝ) + 1) := abs_of_nonneg hNonneg
      _ ≤ δ := hLe
  simpa only [Real.norm_eq_abs, R, B, δ] using
    (MeasureTheory.norm_setIntegral_le_of_norm_le_const hFin hBound)
