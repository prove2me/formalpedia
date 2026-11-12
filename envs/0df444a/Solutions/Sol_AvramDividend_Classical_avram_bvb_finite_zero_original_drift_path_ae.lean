-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_finite_zero_original_drift_path_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T00:56:41.8452+00:00
-- url     : https://prove2.me/submissions/ea07228c-1e9f-47e5-a951-009ed7b28e0b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_finite_zero_original_fixed_clock_drift_probability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X :
  SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (hFinite : X.ν (Iio (0 : ℝ)) < ⊤) (hZero : X.ν (Iio
  (0 : ℝ)) = 0) : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, X.X t ω = (t : ℝ) * X.drift := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hRat (r : ℚ) :
      ∀ᵐ ω ∂P, X.X (Real.toNNReal (r : ℝ)) ω =
        ((Real.toNNReal (r : ℝ) : ℝ≥0) : ℝ) * X.drift := by
    let t : ℝ≥0 := Real.toNNReal (r : ℝ)
    have hm : MeasurableSet {ω : Ω | X.X t ω = (t : ℝ) * X.drift} :=
      by
      have hXm : Measurable (X.X t) := X.adapted.measurable
      exact measurableSet_eq_fun hXm measurable_const
    have hprob : P {ω : Ω | X.X t ω = (t : ℝ) * X.drift} = 1 := by
      have h := avram_bvb_finite_zero_original_fixed_clock_drift_probability
        X hBV hFinite hZero t
      exact (ENNReal.toReal_eq_one_iff _).mp (by simpa only [measureReal_def] using h)
    exact (mem_ae_iff_prob_eq_one hm).mpr hprob
  have hAll : ∀ᵐ ω ∂P, ∀ r : ℚ,
      X.X (Real.toNNReal (r : ℝ)) ω =
        ((Real.toNNReal (r : ℝ) : ℝ≥0) : ℝ) * X.drift :=
    MeasureTheory.ae_all_iff.mpr hRat
  filter_upwards [hAll] with ω hω t
  obtain ⟨u, _, huGT, huT⟩ :=
    Real.exists_seq_rat_strictAnti_tendsto (t : ℝ)
  let v : ℕ → ℝ≥0 := fun n => Real.toNNReal (u n : ℝ)
  have hvT : Tendsto v atTop (𝓝 t) := by
    simpa only [Real.toNNReal_coe] using (tendsto_real_toNNReal huT)
  have hvGE (n : ℕ) : t ≤ v n := by
    simpa only [Real.toNNReal_coe] using
      (Real.toNNReal_monotone (le_of_lt (huGT n)))
  have hvWithin : Tendsto v atTop (𝓝[Set.Ici t] t) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hvT, Filter.Eventually.of_forall (fun n => hvGE n)⟩
  have hXt : Tendsto (fun n => X.X (v n) ω)
      atTop (𝓝 (X.X t ω)) :=
    (X.rightCont ω t).tendsto.comp hvWithin
  have hlin : Tendsto (fun n => (v n : ℝ) * X.drift)
      atTop (𝓝 ((t : ℝ) * X.drift)) := by
    have hc : Continuous (fun s : ℝ≥0 => (s : ℝ) * X.drift) :=
      continuous_subtype_val.mul continuous_const
    exact (hc.tendsto t).comp hvT
  have heq (n : ℕ) :
      X.X (v n) ω = (v n : ℝ) * X.drift := hω (u n)
  have hlin' : Tendsto (fun n => (v n : ℝ) * X.drift)
      atTop (𝓝 (X.X t ω)) :=
    hXt.congr' (Filter.Eventually.of_forall heq)
  exact tendsto_nhds_unique hlin' hlin
