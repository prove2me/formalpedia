-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_BV_mass_positive_DCT_for_random_errors
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:25:28.957579+00:00
-- url     : https://prove2.me/submissions/b659f1e8-7679-4f6d-874e-9ecdc4df1ea1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_BV_source_variation_L1_upto_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Any error genuinely dominated by the original BV physical source mass
has vanishing positive expected part once its a.e. convergence is proved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (hT : T ≤ 1)
    (K : ℝ) (hK : 0 ≤ K)
    (Err : ℕ → Ω → ℝ)
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P)
    (hErrAE : ∀ᵐ ω ∂P,
      Tendsto (fun m => Err m ω) atTop (nhds (0 : ℝ)))
    (hDom : ∀ m, ∀ᵐ ω ∂P,
      ‖Err m ω‖ ≤ K * (|X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|)) :
    (∀ m, Integrable (fun ω => max (Err m ω) 0) P) ∧
    Tendsto (fun m => ∫ ω, max (Err m ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let H : Ω → ℝ := fun ω =>
    K * (|X.drift| * (T : ℝ) +
      |(T : ℝ) * X.drift - X.X T ω|)
  have hB : Integrable (fun ω =>
      |X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|) P :=
    (avram_bv_error7_original_BV_source_variation_L1_upto_one
      X hX hBV T hT).1
  have hH : Integrable H P := hB.const_mul K
  have hErrInt (m : ℕ) : Integrable (Err m) P :=
    hH.mono' (hErrMeas m) (hDom m)
  have hPosInt (m : ℕ) :
      Integrable (fun ω => max (Err m ω) 0) P := by
    have hAbs : Integrable (fun ω => |Err m ω|) P :=
      (hErrInt m).abs
    have hPlus : Integrable (fun ω => Err m ω + |Err m ω|) P :=
      (hErrInt m).add hAbs
    have hHalf : Integrable
        (fun ω => (1 / 2 : ℝ) * (Err m ω + |Err m ω|)) P :=
      hPlus.const_mul (1 / 2 : ℝ)
    have hrepr : (fun ω => max (Err m ω) 0) =
        (fun ω => (1 / 2 : ℝ) * (Err m ω + |Err m ω|)) := by
      funext ω
      rcases le_total (Err m ω) 0 with hn | hp
      · rw [max_eq_right hn, abs_of_nonpos hn]
        ring
      · rw [max_eq_left hp, abs_of_nonneg hp]
        ring
    rw [hrepr]
    exact hHalf
  have hPosDom (m : ℕ) :
      ∀ᵐ ω ∂P, ‖max (Err m ω) 0‖ ≤ H ω := by
    filter_upwards [hDom m] with ω hω
    have hnorm : |max (Err m ω) 0| ≤ |Err m ω| := by
      rcases le_total (Err m ω) 0 with hn | hp
      · rw [max_eq_right hn]
        simp
      · rw [max_eq_left hp]
    have hnorm' : ‖max (Err m ω) 0‖ ≤ ‖Err m ω‖ := by
      simpa only [Real.norm_eq_abs] using hnorm
    exact hnorm'.trans hω
  have hPosAE : ∀ᵐ ω ∂P,
      Tendsto (fun m => max (Err m ω) 0) atTop
        (nhds (0 : ℝ)) := by
    filter_upwards [hErrAE] with ω hω
    simpa using hω.max (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  refine ⟨hPosInt, ?_⟩
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    H (fun m => (hPosInt m).aestronglyMeasurable) hH hPosDom hPosAE
  simpa using hDCT
