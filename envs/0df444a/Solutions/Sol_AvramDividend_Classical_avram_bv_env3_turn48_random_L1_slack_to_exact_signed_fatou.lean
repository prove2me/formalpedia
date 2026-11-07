-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn48_random_L1_slack_to_exact_signed_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T07:50:57.220698+00:00
-- url     : https://prove2.me/submissions/576fe231-8467-4d1e-bed3-c0505d043637

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_source_slack_exact_signed_fatou_normalisation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Absorb physical random L1 grid errors into centred signed sources. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (w : ℝ) (hw : 0 < w) (Y : Ω → ℝ)
    (F M B E : ℕ → Ω → ℝ)
    (hFm : ∀ n, Measurable (F n))
    (hFi : ∀ n, Integrable (F n) P)
    (hFn : ∀ n, 0 ≤ᵐ[P] F n)
    (hR : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
      (∫ ω, M n ω + B n ω ∂P) ≤ 0)
    (hEi : ∀ n, Integrable (E n) P)
    (hEn : ∀ n, 0 ≤ᵐ[P] E n)
    (hE0 : Tendsto (fun n => ∫ ω, E n ω ∂P) atTop (nhds 0))
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w + (M n ω + B n ω) + E n ω)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    ∃ F' M' B' : ℕ → Ω → ℝ,
      (∀ n, Measurable (F' n) ∧ Integrable (F' n) P ∧
        0 ≤ᵐ[P] F' n) ∧
      (∀ n, Integrable (fun ω => M' n ω + B' n ω) P ∧
        (∫ ω, M' n ω + B' n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P, F' n ω ≤
        w + (M' n ω + B' n ω)) ∧
      (∀ᵐ ω ∂P, ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F' n ω)) atTop) := by
  let e : ℕ → ℝ := fun n => ∫ ω, E n ω ∂P
  have he : ∀ n, 0 ≤ e n := fun n => integral_nonneg_of_ae (hEn n)
  have he0 : Tendsto e atTop (nhds (0 : ℝ)) := hE0
  let R : ℕ → Ω → ℝ := fun n ω =>
    (M n ω + B n ω) + E n ω - e n
  have hRi : ∀ n, Integrable (R n) P := by
    intro n
    exact ((hR n).1.add (hEi n)).sub (integrable_const _)
  have hRm : ∀ n, (∫ ω, R n ω ∂P) ≤ 0 := by
    intro n
    have hsplit : (∫ ω, R n ω ∂P) =
        (∫ ω, M n ω + B n ω ∂P) +
          (∫ ω, E n ω ∂P) - e n := by
      have hsub : (∫ ω, R n ω ∂P) =
          (∫ ω, (M n ω + B n ω) + E n ω ∂P) - e n := by
        simpa [R] using
          (integral_sub ((hR n).1.add (hEi n)) (integrable_const (e n)))
      have hadd : (∫ ω, (M n ω + B n ω) + E n ω ∂P) =
          (∫ ω, M n ω + B n ω ∂P) + (∫ ω, E n ω ∂P) := by
        simpa only [Pi.add_apply] using integral_add (hR n).1 (hEi n)
      rw [hsub, hadd]
    rw [hsplit]
    simpa only [e, add_sub_cancel_right] using (hR n).2
  have hBound : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w + (R n ω + 0) + e n := by
    intro n
    filter_upwards [hPath n] with ω hω
    dsimp [R]
    linarith
  exact avram_p3_grid4_source_slack_exact_signed_fatou_normalisation
    P w hw Y F R (fun _ _ => 0) e he he0
    hFm hFi hFn (fun n => ⟨by simpa using hRi n, by simpa using hRm n⟩)
    hBound hFatou
