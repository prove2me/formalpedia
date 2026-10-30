-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_actual_Qp_upper_record_strict_weak_clock_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:36:18.713985+00:00
-- url     : https://prove2.me/submissions/f20db403-62ab-4aeb-afd6-07ff9a2085f5

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_real_exp_clock_record_age_tie_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- True Esscher terminal observation cannot tie the source first strict
upper-record age; weak versus strict record-before-clock is immaterial. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (b θ p : ℝ) (hb : 0 ≤ b) (hθ : 0 ≤ θ) (hp : 0 < p)
    (R : Ω × ℝ → ℝ≥0∞) (hR : Measurable R) :
    (let age : Ω → ℝ≥0 := fun ω => (twoSidedExitUpTime X b ω).toNNReal
     let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z => ENNReal.ofReal (Real.exp
           (θ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * X.ψ θ)))
     (∫⁻ z, ({z : Ω × ℝ | 0 ≤ z.2 ∧
       twoSidedExitUpTime X b z.1 < ⊤ ∧
       (age z.1 : ℝ) ≤ z.2}).indicator R z ∂Qp) =
     (∫⁻ z, ({z : Ω × ℝ | 0 ≤ z.2 ∧
       twoSidedExitUpTime X b z.1 < ⊤ ∧
       (age z.1 : ℝ) < z.2}).indicator R z ∂Qp)) := by
  intro age Qp
  have hNull : Qp {z : Ω × ℝ | z.2 = (age z.1 : ℝ)} = 0 := by
    simpa only [Qp, age] using
      avram_ws01e_b_actual_Qp_real_exp_clock_record_age_tie_zero
        X b θ p hb hθ hp
  have hAE : ∀ᵐ z : Ω × ℝ ∂Qp,
      z ∉ {z : Ω × ℝ | z.2 = (age z.1 : ℝ)} := by
    apply (ae_iff).2
    simpa only [Set.mem_setOf_eq, not_not] using hNull
  apply lintegral_congr_ae
  filter_upwards [hAE] with z hz
  have hne : z.2 ≠ (age z.1 : ℝ) := by
    simpa only [Set.mem_setOf_eq] using hz
  have hiff :
      (0 ≤ z.2 ∧ twoSidedExitUpTime X b z.1 < ⊤ ∧
        (age z.1 : ℝ) ≤ z.2) ↔
      (0 ≤ z.2 ∧ twoSidedExitUpTime X b z.1 < ⊤ ∧
        (age z.1 : ℝ) < z.2) := by
    constructor
    · rintro ⟨hr0, ht, hle⟩
      exact ⟨hr0, ht, lt_of_le_of_ne hle (Ne.symm hne)⟩
    · rintro ⟨hr0, ht, hlt⟩
      exact ⟨hr0, ht, hlt.le⟩
  by_cases hweak : 0 ≤ z.2 ∧ twoSidedExitUpTime X b z.1 < ⊤ ∧
      (age z.1 : ℝ) ≤ z.2
  · have hstrict := hiff.mp hweak
    simp [Set.indicator, hweak, hstrict]
  · have hstrict : ¬ (0 ≤ z.2 ∧ twoSidedExitUpTime X b z.1 < ⊤ ∧
      (age z.1 : ℝ) < z.2) := fun h => hweak (hiff.mpr h)
    simp [Set.indicator, hweak, hstrict]
