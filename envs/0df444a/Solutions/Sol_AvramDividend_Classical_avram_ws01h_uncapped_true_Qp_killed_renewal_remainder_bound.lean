-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_uncapped_true_Qp_killed_renewal_remainder_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T12:51:17.253995+00:00
-- url     : https://prove2.me/submissions/c930ba87-3bbc-41fe-a4c8-628a1d64e849

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_uncapped_original_levy_survival_record_mass_partition
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_Qp_weak_noRecord_mass_le_exponential_cdf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Exact full-horizon genuine Esscher Qp lower-killed first-record CDF
renewal remainder, with no stopping cap and no exit-ratio assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q : ℝ) (hφ : 0 < φ) (hq : 0 < q) (hroot : X.ψ φ = q)
    (p : ℝ) (hp : 0 < p) (lam : ℝ) (hlam : 0 < lam)
    (hshift : X.ψ (φ + lam) - q = p)
    (x b : ℝ) (hb : 0 ≤ b) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (φ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * q)))
     let age : Ω → ℝ≥0 := fun ω =>
       (twoSidedExitUpTime X b ω).toNNReal
     let E : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
     let A : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
       twoSidedExitUpTime X b z.1 < (Real.toNNReal z.2 : ℝ≥0∞) ∧
       twoSidedExitUpTime X b z.1 < twoSidedExitDownTime X (-x) z.1 ∧
       ∀ u : ℝ≥0, u ≤ Real.toNNReal z.2 - age z.1 →
          0 ≤ (x + b) + (X.X (age z.1 + u) z.1 - X.X (age z.1) z.1)}
     Qp A ≤ Qp E ∧
       Qp E ≤ Qp A + (expMeasure lam) (Iic b)) := by
  intro Qp age E A
  let B : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
    (Real.toNNReal z.2 : ℝ≥0∞) ≤ twoSidedExitUpTime X b z.1 ∧
    ∀ s : ℝ≥0, s ≤ Real.toNNReal z.2 → -x ≤ X.X s z.1}
  have hMass : Qp E = Qp A + Qp B := by
    simpa only [Qp, age, E, A, B] using
      (avram_ws01h_uncapped_original_levy_survival_record_mass_partition
        X x b hb Qp)
  have hBound : Qp B ≤ (expMeasure lam) (Iic b) := by
    have hSub : B ⊆ {z : Ω × ℝ | 0 ≤ z.2 ∧
        (Real.toNNReal z.2 : ℝ≥0∞) ≤
          twoSidedExitUpTime X b z.1} := by
      intro z hz
      exact ⟨hz.1, hz.2.1⟩
    calc
      Qp B ≤ Qp {z : Ω × ℝ | 0 ≤ z.2 ∧
          (Real.toNNReal z.2 : ℝ≥0∞) ≤
            twoSidedExitUpTime X b z.1} := measure_mono hSub
      _ ≤ (expMeasure lam) (Iic b) := by
        simpa only [Qp] using
          (avram_ws01h_Qp_weak_noRecord_mass_le_exponential_cdf
            X φ q hφ hq hroot p hp lam hlam hshift b hb)
  constructor
  · rw [hMass]
    exact le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ Qp B from bot_le)
  · rw [hMass]
    exact add_le_add_right hBound (Qp A)
