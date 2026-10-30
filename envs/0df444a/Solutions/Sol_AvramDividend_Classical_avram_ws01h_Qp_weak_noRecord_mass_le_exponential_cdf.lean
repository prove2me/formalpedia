-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01h_Qp_weak_noRecord_mass_le_exponential_cdf
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T11:07:40.401966+00:00
-- url     : https://prove2.me/submissions/edd83990-dd71-484f-b5ec-7ddcc755a3fd

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01h_Qp_noRecord_mass_le_exponential_cdf
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_Qp_real_exp_clock_record_age_tie_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

/-- Under the true tilted joint exponential clock, the weak no-record
remainder has the same exponential-supremum CDF bound as strict no-record.
The real clock tie at the upper age is genuinely Qp-null. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (φ q : ℝ) (hφ : 0 < φ) (hq : 0 < q) (hroot : X.ψ φ = q)
    (p : ℝ) (hp : 0 < p) (lam : ℝ) (hlam : 0 < lam)
    (hshift : X.ψ (φ + lam) - q = p)
    (b : ℝ) (hb : 0 ≤ b) :
    (let Qp : Measure (Ω × ℝ) :=
       (P.prod (ProbabilityTheory.expMeasure p)).withDensity
         (fun z : Ω × ℝ => ENNReal.ofReal (Real.exp
           (φ * X.X (Real.toNNReal z.2) z.1 -
             (Real.toNNReal z.2 : ℝ) * q)))
     Qp {z : Ω × ℝ | 0 ≤ z.2 ∧
       (Real.toNNReal z.2 : ℝ≥0∞) ≤
         twoSidedExitUpTime X b z.1} ≤
       (ProbabilityTheory.expMeasure lam) (Iic b)) := by
  intro Qp
  let age : Ω → ℝ≥0 := fun ω =>
    (twoSidedExitUpTime X b ω).toNNReal
  let A : Set (Ω × ℝ) := {z |
    (Real.toNNReal z.2 : ℝ≥0∞) <
      twoSidedExitUpTime X b z.1}
  let B : Set (Ω × ℝ) := {z |
    z.2 = (age z.1 : ℝ)}
  let E : Set (Ω × ℝ) := {z | 0 ≤ z.2 ∧
    (Real.toNNReal z.2 : ℝ≥0∞) ≤
      twoSidedExitUpTime X b z.1}
  have hTie : Qp B = 0 := by
    dsimp [Qp, B, age]
    rw [← hroot]
    exact avram_ws01e_b_actual_Qp_real_exp_clock_record_age_tie_zero
      X b φ p hb hφ.le hp
  have hBound : Qp A ≤ (expMeasure lam) (Iic b) := by
    simpa only [Qp, A] using
      (avram_ws01h_Qp_noRecord_mass_le_exponential_cdf
        X φ q hφ hq hroot p hp lam hlam hshift b hb)
  have hSubset : E ⊆ A ∪ B := by
    intro z hz
    change 0 ≤ z.2 ∧ (Real.toNNReal z.2 : ℝ≥0∞) ≤
      twoSidedExitUpTime X b z.1 at hz
    rcases lt_or_eq_of_le hz.2 with hlt | heq
    · exact Or.inl hlt
    · right
      have hAge : Real.toNNReal z.2 = age z.1 := by
        have h := congrArg ENNReal.toNNReal heq
        simpa only [age, ENNReal.toNNReal_coe] using h
      change z.2 = ((age z.1 : ℝ≥0) : ℝ)
      calc
        z.2 = (Real.toNNReal z.2 : ℝ) :=
          (Real.coe_toNNReal z.2 hz.1).symm
        _ = (age z.1 : ℝ) :=
          congrArg (fun v : ℝ≥0 => (v : ℝ)) hAge
  calc
    Qp E ≤ Qp (A ∪ B) := measure_mono hSubset
    _ ≤ Qp A + Qp B := measure_union_le _ _
    _ = Qp A := by rw [hTie, add_zero]
    _ ≤ (expMeasure lam) (Iic b) := hBound
