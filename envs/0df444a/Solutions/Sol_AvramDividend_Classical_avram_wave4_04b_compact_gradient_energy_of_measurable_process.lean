-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_compact_gradient_energy_of_measurable_process
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:56:35.071703+00:00
-- url     : https://prove2.me/submissions/5638be99-288c-4a64-870f-6fd1654ad7b7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_measurable_interior_deriv_zero_extension
import Theorems.Thm_AvramDividend_Classical_derivative_abs_le_on_compact_interior_interval

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal Classical
noncomputable section

/-- C² on an open reserve interval gives uniform finite quadratic energy on compact bands. -/
theorem solution
    {A : Type*} [MeasurableSpace A]
    (Y : A → ℝ) (hY : Measurable Y)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : Measure A) (hμ : μ Set.univ < ⊤) :
    Measurable (fun p : A =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0) ∧
      (∫⁻ p : A, ENNReal.ofReal
        ((if Y p ∈ Icc u v then deriv w (Y p) else 0) ^ 2) ∂μ) < ⊤ := by
  classical
  have hd : Measurable (fun y : ℝ =>
      if y ∈ Ioo a b then deriv w y else 0) := by
    convert avram_wave4_04b_measurable_interior_deriv_zero_extension
      w (Ioo a b) isOpen_Ioo hw using 1
    funext y
    split_ifs <;> rfl
  have hinside : Measurable (fun p : A =>
      if Y p ∈ Ioo a b then deriv w (Y p) else 0) :=
    hd.comp hY
  have hband : MeasurableSet {p : A | Y p ∈ Icc u v} :=
    measurableSet_Icc.preimage hY
  have hHmeas : Measurable (fun p : A =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0) := by
    have heq : (fun p : A =>
        if Y p ∈ Icc u v then deriv w (Y p) else 0) =
      (fun p : A =>
        if Y p ∈ Icc u v then
          (if Y p ∈ Ioo a b then deriv w (Y p) else 0) else 0) := by
      funext p
      by_cases hp : Y p ∈ Icc u v
      · have hp' : Y p ∈ Ioo a b :=
          ⟨lt_of_lt_of_le hau hp.1, lt_of_le_of_lt hp.2 hvb⟩
        simp [hp, hp']
      · simp [hp]
    rw [heq]
    exact hinside.ite hband measurable_const
  have hw1 : ContDiffOn ℝ 1 w (Ioo a b) := hw.of_le (by norm_num)
  obtain ⟨M, hM, hderiv⟩ :=
    derivative_abs_le_on_compact_interior_interval
      w a b u v hw1 hau huv hvb
  have hbound (p : A) :
      ((if Y p ∈ Icc u v then deriv w (Y p) else 0) ^ 2) ≤ M ^ 2 := by
    by_cases hp : Y p ∈ Icc u v
    · have hAbs := hderiv (Y p) hp.1 hp.2
      have hlo := (abs_le.mp hAbs).1
      have hhi := (abs_le.mp hAbs).2
      have ha : 0 ≤ M - deriv w (Y p) := by linarith
      have hb : 0 ≤ M + deriv w (Y p) := by linarith
      simp only [if_pos hp]
      nlinarith [mul_nonneg ha hb]
    · simp [hp, sq_nonneg M]
  refine ⟨hHmeas, ?_⟩
  have hfinite : μ Set.univ * ENNReal.ofReal (M ^ 2) < ⊤ :=
    ENNReal.mul_lt_top hμ ENNReal.ofReal_lt_top
  calc
    (∫⁻ p : A, ENNReal.ofReal
      ((if Y p ∈ Icc u v then deriv w (Y p) else 0) ^ 2) ∂μ) ≤
        ∫⁻ _ : A, ENNReal.ofReal (M ^ 2) ∂μ := by
          apply lintegral_mono
          intro p
          exact ENNReal.ofReal_le_ofReal (hbound p)
    _ = μ Set.univ * ENNReal.ofReal (M ^ 2) := by simp [mul_comm]
    _ < ⊤ := hfinite
