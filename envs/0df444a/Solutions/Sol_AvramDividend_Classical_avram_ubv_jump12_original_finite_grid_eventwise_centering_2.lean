-- Prove2me | solution 2 for AvramDividend.Classical.avram_ubv_jump12_original_finite_grid_eventwise_centering
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T13:34:00.131805+00:00
-- url     : https://prove2.me/submissions/309c14df-fe3f-4d64-92d2-5d459868cb14

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_weighted_finite_band_L1_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_original_finite_band_past_event_integral_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ι → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (r : ι → ℕ → ℝ≥0)
    (hsr : ∀ i n, s i < r i n) (hrt : ∀ i n, r i n ≤ t i)
    (hShort : ∀ i, Tendsto (fun n => r i n - s i) atTop (𝓝 0))
    (hLong : ∀ i, Tendsto (fun n => t i - r i n) atTop (𝓝 (t i - s i)))
    (B : ι → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (hFinite : ∀ i, X.ν (B i) < ⊤)
    (J : ι → Ω → ℝ≥0∞)
    (hJsource : ∀ i ω, J i ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc (s i) (t i) ×ˢ B i))
    (H : ι → Ω → ℝ) (K : ι → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕.rightCont (s i)] (H i))
    (hHAE : ∀ i, AEStronglyMeasurable (H i) P)
    (hBound : ∀ i, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ K i)
    (A : Set Ω) (hA : ∀ i, MeasurableSet[𝓕.rightCont (s i)] A) :
    (∫ ω in A, ∑ i : ι, H i ω *
      ((J i ω).toReal -
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal) ∂P) = 0 := by
  classical
  let G : ι → Ω → ℝ := fun i ω =>
    H i ω * ((J i ω).toReal -
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)
  have hIntegrable (i : ι) : Integrable (G i) (P.restrict A) := by
    have hFull : Integrable (G i) P := by
      dsimp [G]
      exact (AvramDividend.Classical.avram_ubv_jump11_original_weighted_finite_band_L1_condexp_zero
        X (s i) (t i) (hst i) (r i) (hsr i) (hrt i)
        (hShort i) (hLong i) (B i) (hB i) (hFinite i)
        (J i) (hJsource i) (H i) (K i)
        (hH i) (hHAE i) (hBound i)).1
    exact hFull.integrableOn
  change (∫ ω in A, ∑ i : ι, G i ω ∂P) = 0
  calc
    (∫ ω in A, ∑ i : ι, G i ω ∂P)
        = ∑ i : ι, ∫ ω in A, G i ω ∂P := by
            exact MeasureTheory.integral_finset_sum Finset.univ
              (by intro i hi; exact hIntegrable i)
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      change (∫ ω in A, H i ω * ((J i ω).toReal -
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal) ∂P) = 0
      exact AvramDividend.Classical.avram_ubv_jump11_original_finite_band_past_event_integral_zero
        X (s i) (t i) (hst i) (r i) (hsr i) (hrt i)
        (hShort i) (hLong i) (B i) (hB i) (hFinite i)
        (J i) (hJsource i) (H i) (K i)
        (hH i) (hHAE i) (hBound i) A (hA i)
