-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_bv_positive_ruin_strict_stopped_drift_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T11:12:30.343344+00:00
-- url     : https://prove2.me/submissions/be6cd67b-aea9-4923-8705-dc0bb04326f2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_uniform_preRuin_full_stieltjes_drift_envelope
import Theorems.Thm_AvramDividend_Classical_paymentTimes_lintegral_le_of_rational_prefix_bounds
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Every path with positive ruin time has its entire strict stopped dividend
    Stieltjes reward controlled by the original BV drift allowance, including
    when ruin occurs before the chosen deterministic horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (H : ℝ≥0) (hH : 0 < H) :
    ∀ᵐ ω ∂P, 0 < ruinTime X x D ω →
      (∫⁻ r in paymentTimes
          (min (ruinTime X x D ω) (H : ℝ≥0∞)),
        ENNReal.ofReal (Real.exp (-(q * r)))
          ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (x + (H : ℝ) * X.drift) := by
  have hdrift : 0 ≤ X.drift := (bv_standing_drift_pos X hX hBV).1.le
  filter_upwards
      [avram_wave3_03_bv_uniform_preRuin_full_stieltjes_drift_envelope
        X hBV x D hD q hq] with ω huniform
  intro hruin
  have hHtop : (0 : ℝ≥0∞) < (H : ℝ≥0∞) := by exact_mod_cast hH
  have hstop : (0 : ℝ≥0∞) <
      min (ruinTime X x D ω) (H : ℝ≥0∞) := lt_min hruin hHtop
  apply paymentTimes_lintegral_le_of_rational_prefix_bounds
    (dividendMeasure D ω)
    (fun r : ℝ => ENNReal.ofReal (Real.exp (-(q * r))))
    (min (ruinTime X x D ω) (H : ℝ≥0∞))
    (ENNReal.ofReal (x + (H : ℝ) * X.drift)) hstop
  intro r
  let T : ℝ≥0 := ⟨(r.val : ℝ), r.property.1.le⟩
  have hT_eq : (T : ℝ≥0∞) = ENNReal.ofReal (r.val : ℝ) := by
    change (T : ℝ≥0∞) = ENNReal.ofReal (T : ℝ)
    simp only [ENNReal.ofReal_coe_nnreal]
  have hT : (T : ℝ≥0∞) < ruinTime X x D ω := by
    have hh := lt_of_lt_of_le r.property.2 (min_le_left _ _)
    rw [hT_eq]
    exact hh
  have hTH : T ≤ H := by
    have hh := lt_of_lt_of_le r.property.2 (min_le_right _ _)
    have hhh : (T : ℝ≥0∞) < (H : ℝ≥0∞) := by
      rw [hT_eq]
      exact hh
    exact le_of_lt (by exact_mod_cast hhh)
  have hsub : Ico (0 : ℝ) (r.val : ℝ) ⊆
      paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ) := by
    intro t ht
    constructor
    · simp only [paymentTimes, Set.mem_setOf_eq]
      refine ⟨ht.1, Or.inr ?_⟩
      exact (ENNReal.ofReal_le_ofReal (le_of_lt ht.2)).trans_lt
        (by rw [← hT_eq]; exact hT)
    · exact le_of_lt ht.2
  calc
    (∫⁻ t in Ico (0 : ℝ) (r.val : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
        lintegral_mono_set hsub
    _ ≤ ENNReal.ofReal (x + (T : ℝ) * X.drift) :=
      huniform T (ruinTime X x D ω) hT
    _ ≤ ENNReal.ofReal (x + (H : ℝ) * X.drift) := by
      apply ENNReal.ofReal_le_ofReal
      have ht : (T : ℝ) ≤ (H : ℝ) := by exact_mod_cast hTH
      nlinarith
