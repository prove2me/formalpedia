-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_random_positive_source_error_fatou_normalisation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T09:22:58.226261+00:00
-- url     : https://prove2.me/submissions/1368ccc3-5f95-4af3-bf8f-153a6ef43668

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_centered_physical_error_signed_budget
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_source_slack_exact_signed_fatou_normalisation
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A vanishing L¹ positive physical-grid source error can be centred and
rescaled while preserving the original nonpositive-mean signed source. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (w : ℝ) (hw : 0 < w) (Y : Ω → ℝ)
    (F M B Err : ℕ → Ω → ℝ)
    (hMeas : ∀ n, Measurable (F n))
    (hInt : ∀ n, Integrable (F n) P)
    (hPos : ∀ n, 0 ≤ᵐ[P] F n)
    (hSigned : ∀ n, Integrable (fun ω => M n ω + B n ω) P ∧
      (∫ ω, M n ω + B n ω ∂P) ≤ 0)
    (hErrInt : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hErrMean : Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P) atTop (𝓝 0))
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w + (M n ω + B n ω) + max (Err n ω) 0)
    (hFatou : ∀ᵐ ω ∂P,
      ENNReal.ofReal (Y ω) ≤
        liminf (fun n => ENNReal.ofReal (F n ω)) atTop) :
    ∃ F' M' B' : ℕ → Ω → ℝ,
      (∀ n, Measurable (F' n) ∧ Integrable (F' n) P ∧
        0 ≤ᵐ[P] F' n) ∧
      (∀ n, Integrable (fun ω => M' n ω + B' n ω) P ∧
        (∫ ω, M' n ω + B' n ω ∂P) ≤ 0) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F' n ω ≤ w + (M' n ω + B' n ω)) ∧
      (∀ᵐ ω ∂P,
        ENNReal.ofReal (Y ω) ≤
          liminf (fun n => ENNReal.ofReal (F' n ω)) atTop) := by
  let R : ℕ → Ω → ℝ := fun n ω => max (Err n ω) 0
  let e : ℕ → ℝ := fun n => ∫ ω, R n ω ∂P
  let Mc : ℕ → Ω → ℝ := fun n ω =>
    (M n ω + B n ω) + R n ω - e n
  let Bc : ℕ → Ω → ℝ := fun _ _ => 0
  have he : ∀ n, 0 ≤ e n := by
    intro n
    exact integral_nonneg (fun ω => le_max_right (Err n ω) 0)
  have he0 : Tendsto e atTop (𝓝 (0 : ℝ)) := hErrMean
  have hRc : ∀ n, Integrable (R n) P := hErrInt
  have hC :=
    avram_p3_grid4_centered_physical_error_signed_budget P
      (fun n ω => M n ω + B n ω) R hSigned hRc
  have hMc : ∀ n,
      Integrable (fun ω => Mc n ω + Bc n ω) P ∧
      (∫ ω, Mc n ω + Bc n ω ∂P) ≤ 0 := by
    intro n
    simpa only [Mc, Bc, add_zero, e] using hC n
  have hPathC : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ w + (Mc n ω + Bc n ω) + e n := by
    intro n
    filter_upwards [hPath n] with ω hp
    dsimp [Mc, Bc, R, e]
    linarith
  exact avram_p3_grid4_source_slack_exact_signed_fatou_normalisation
    P w hw Y F Mc Bc e he he0
    hMeas hInt hPos hMc hPathC hFatou
