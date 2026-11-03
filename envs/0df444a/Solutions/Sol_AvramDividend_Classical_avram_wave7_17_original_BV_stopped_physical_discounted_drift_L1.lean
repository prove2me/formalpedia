-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_BV_stopped_physical_discounted_drift_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:32:07.40474+00:00
-- url     : https://prove2.me/submissions/c4a3ed68-9c66-434f-9a8c-5f42ddfc0585

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Physical discounted source drift is L¹ on any measurable finite-horizon
ruin-stopped interior, with the original Lévy probability and actual dividend path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (C : ℝ≥0∞)
    (hS : MeasurableSet
      {p : ℝ≥0 × Ω |
        p.1 ≤ T ∧
        (p.1 : ℝ≥0∞) < ruinTime X x D p.2 ∧
        0 < Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
        ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1) < C}) :
    let μ : Measure (ℝ≥0 × Ω) :=
      ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
    let S : Set (ℝ≥0 × Ω) :=
      {p | p.1 ≤ T ∧ (p.1 : ℝ≥0∞) < ruinTime X x D p.2 ∧
        0 < Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
        ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
          x + X.X s p.2 - rightLimit D s p.2) p.1) < C}
    IntegrableOn
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ))) * X.drift) S μ := by
  dsimp only
  letI : IsProbabilityMeasure P := X.isProbability
  let μtime : Measure ℝ≥0 :=
    ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
  haveI hμtime : IsFiniteMeasure μtime := by
    dsimp [μtime]
    exact Measure.isFiniteMeasure_map _ Real.toNNReal
  let μ : Measure (ℝ≥0 × Ω) := μtime.prod P
  haveI hμ : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  let S : Set (ℝ≥0 × Ω) :=
    {p | p.1 ≤ T ∧ (p.1 : ℝ≥0∞) < ruinTime X x D p.2 ∧
      0 < Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1 ∧
      ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s p.2 - rightLimit D s p.2) p.1) < C}
  have hsfinite : μ S < ⊤ :=
    lt_of_le_of_lt (measure_mono (subset_univ S)) (measure_lt_top μ Set.univ)
  have hfmeas : Measurable
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ))) * X.drift) := by
    fun_prop
  have hfbound : ∀ p : ℝ≥0 × Ω,
      ‖Real.exp (-(q * (p.1 : ℝ))) * X.drift‖ ≤ |X.drift| := by
    intro p
    have hqtime : 0 ≤ q * (p.1 : ℝ) :=
      mul_nonneg hq p.1.property
    have he : Real.exp (-(q * (p.1 : ℝ))) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqtime)
    have hmul := mul_le_mul_of_nonneg_right he (abs_nonneg X.drift)
    simpa only [Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos (-(q * (p.1 : ℝ)))), one_mul] using hmul
  have hres : IntegrableOn
      (fun p : ℝ≥0 × Ω => Real.exp (-(q * (p.1 : ℝ))) * X.drift) S μ :=
    IntegrableOn.of_bound hsfinite hfmeas.aestronglyMeasurable |X.drift|
      (Filter.Eventually.of_forall hfbound)
  simpa only [μ, μtime, S] using hres
