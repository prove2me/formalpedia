-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f12_original_zero_clock_mask_dominates_unmasked_mean
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T00:16:52.698581+00:00
-- url     : https://prove2.me/submissions/94e0d02e-3d93-438d-b5b4-7a65836db0fd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_zero_clock_exact_physical_F_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- At the original zero clock, physical F cannot exceed the masked value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hzero_meas : ∀ k, MeasurableSet {ω : Ω | σ k ω = 0}) :
    ∀ k, (∫ ω, F k ω ∂P) ≤
      ∫ ω, (if σ k ω = 0 then w x else F k ω) ∂P := by
  intro k
  classical
  let A : Set Ω := {ω | σ k ω = 0}
  have hA : MeasurableSet A := hzero_meas k
  have hb : Integrable (fun _ : Ω => w x) P := integrable_const (w x)
  have hI : Integrable (A.indicator (fun ω => w x - F k ω)) P :=
    (hb.sub (hFI k)).indicator hA
  have hMask : Integrable (fun ω => if σ k ω = 0 then w x else F k ω) P := by
    have hFun : (fun ω => if σ k ω = 0 then w x else F k ω) =
        (fun ω => F k ω + A.indicator (fun ω => w x - F k ω) ω) := by
      funext ω
      by_cases h : σ k ω = 0
      · simp [A, Set.indicator, h]
      · simp [A, Set.indicator, h]
    rw [hFun]
    exact (hFI k).add hI
  apply integral_mono (hFI k) hMask
  intro ω
  by_cases h : σ k ω = 0
  · simpa [h] using
      avram_ubv_loc6_original_zero_clock_exact_physical_F_le
        X x q w C D hD hjump σ F hFsource k ω h
  · simp [h]
