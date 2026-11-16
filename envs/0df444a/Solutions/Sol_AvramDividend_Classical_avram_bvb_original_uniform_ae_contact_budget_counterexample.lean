-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_original_uniform_ae_contact_budget_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:47:34.795723+00:00
-- url     : https://prove2.me/submissions/017fb1db-9ccf-49b3-98fc-44e3c2e38848

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_BV_positive_nojump_path_witness
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_source_physical_drift_only_nonconvergence
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_unit_drift_zero_barrier_nojump_survives_tenth
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem solution :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.BoundedVariation ∧
      X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0) ∧
      X.ν (Iio (0 : ℝ)) < ⊤ ∧ X.drift = 1 ∧ X.σ = 0 ∧
      0 < P {ω | ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ Iio (0 : ℝ)) = 0 ∧
        (∀ t : ℝ≥0, t ≤ (1 : ℝ≥0) → X.X t ω = (t : ℝ) * X.drift)} ∧
      (let D := barrierStrategy X 0 0
       let T : ℝ := 1 / 10
       let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
       let u : ℕ → ℕ → ℝ≥0 := fun n i =>
         ⟨(1 / 10 : ℝ) * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
       let F : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun n ω =>
         (∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iio (T - T / ((n : ℝ) + 2)),
           ENNReal.ofReal (Real.exp (-t)) ∂(dividendMeasure D ω)).toReal +
           (if ((1 / 10 : ℝ≥0) : ℝ≥0∞) < ruinTime X 0 D ω then
             Real.exp (-T) * w (riskProcess X 0 D (1 / 10 : ℝ≥0) ω)
            else 0)
       let L : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun n ω =>
         let Z : ℕ → ℝ := fun i => Function.leftLim
           (fun t : ℝ≥0 => (0 : ℝ) + X.X t ω - rightLimit D t ω) (u n i)
         ∑ i ∈ Finset.range (n + 1), if (u n i : ℝ≥0∞) < ruinTime X 0 D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < (1 : ℝ≥0∞) then
             Real.exp (-(u n i : ℝ)) * (X.drift * deriv w (Z i) - w (Z i)) *
               ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0

       ¬ (∀ᵐ ω ∂P, Tendsto (fun n => if ruinTime X 0 D ω = 0 then 0
           else max (F n ω - (w 0 + L n ω)) 0)
           atTop (𝓝 (0 : ℝ)))) := by
  obtain ⟨P, 𝓕, X, hs, hbv, hν, hFinite, hDrift, hσ, hPositive⟩ :=
    avram_bvb_obstruction_original_uniform_BV_positive_nojump_path_witness
      (1 : ℝ≥0)
  let E : Set ((ℕ → ℝ) × (ℕ → ℝ)) := {ω |
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 (1 : ℝ≥0) ×ˢ Iio (0 : ℝ)) = 0 ∧
    (∀ t : ℝ≥0, t ≤ 1 → X.X t ω = (t : ℝ) * X.drift)}
  let D := barrierStrategy X 0 0
  let T : ℝ := 1 / 10
  let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
  let u : ℕ → ℕ → ℝ≥0 := fun n i => ⟨(1 / 10 : ℝ) * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
  let F : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩ Iio (T - T / ((n : ℝ) + 2)),
      ENNReal.ofReal (Real.exp (-t)) ∂(dividendMeasure D ω)).toReal +
      (if ((1 / 10 : ℝ≥0) : ℝ≥0∞) < ruinTime X 0 D ω then
        Real.exp (-T) * w (riskProcess X 0 D (1 / 10 : ℝ≥0) ω)
       else 0)
  let L : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun n ω =>
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => (0 : ℝ) + X.X t ω - rightLimit D t ω) (u n i)
    ∑ i ∈ Finset.range (n + 1), if (u n i : ℝ≥0∞) < ruinTime X 0 D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < (1 : ℝ≥0∞) then Real.exp (-(u n i : ℝ)) *
          (X.drift * deriv w (Z i) - w (Z i)) * ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0
  have hBad : ∀ ω ∈ E,
      ¬ Tendsto (fun n => max (F n ω - (w 0 + L n ω)) 0) atTop (𝓝 (0 : ℝ)) := by
    intro ω hω
    have hPath := hω.2
    have hSource :=
      avram_bvb_obstruction_original_uniform_source_physical_drift_only_nonconvergence
        X ω hDrift hPath
    simpa only [F, L, w, D, T, u] using hSource
  have hSurvive : ∀ ω ∈ E,
      ruinTime X 0 D ω ≠ 0 := by
    intro ω hω
    have hRu := avram_bvb_obstruction_unit_drift_zero_barrier_nojump_survives_tenth
      X ω hDrift hω.2
    have hTpos : (0 : ℝ≥0∞) < ((1 / 10 : ℝ≥0) : ℝ≥0∞) := by
      norm_num
    exact ne_of_gt (lt_trans hTpos hRu)
  have hNoAE : ¬ (∀ᵐ ω ∂P, Tendsto
      (fun n => if ruinTime X 0 D ω = 0 then 0
        else max (F n ω - (w 0 + L n ω)) 0)
        atTop (𝓝 (0 : ℝ))) := by
    intro hAe
    have hZeroMeasure : P {ω | ¬ Tendsto
        (fun n => if ruinTime X 0 D ω = 0 then 0
          else max (F n ω - (w 0 + L n ω)) 0)
          atTop (𝓝 (0 : ℝ))} = 0 := (ae_iff).mp hAe
    have hSubset : E ⊆ {ω | ¬ Tendsto
        (fun n => if ruinTime X 0 D ω = 0 then 0
          else max (F n ω - (w 0 + L n ω)) 0)
          atTop (𝓝 (0 : ℝ))} := by
      intro ω hω
      simpa [hSurvive ω hω] using hBad ω hω
    have hMono : P E ≤ P {ω | ¬ Tendsto
        (fun n => if ruinTime X 0 D ω = 0 then 0
          else max (F n ω - (w 0 + L n ω)) 0)
          atTop (𝓝 (0 : ℝ))} := measure_mono hSubset
    rw [hZeroMeasure] at hMono
    exact (not_le_of_gt hPositive) hMono
  refine ⟨P, 𝓕, X, hs, hbv, hν, hFinite, hDrift, hσ, hPositive, ?_⟩
  simpa only [F, L, D, T, w, u] using hNoAE
