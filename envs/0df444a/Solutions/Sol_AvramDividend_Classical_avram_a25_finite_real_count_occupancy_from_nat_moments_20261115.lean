-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_finite_real_count_occupancy_from_nat_moments_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:06:48.443541+00:00
-- url     : https://prove2.me/submissions/97ec35e2-e6fd-4796-987a-821175017834

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a25_integrated_nat_count_occupancy_factorial_sandwich_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Physical finite ENNReal count occupancy from exact factorial moments. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (N : Ω → ℝ≥0∞) (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) = (N ω).toReal)
    (hFin : ∀ᵐ ω ∂P, N ω < ⊤)
    (r : ℝ)
    (hFirst : Integrable (fun ω => (N ω).toReal) P ∧
      (∫ ω, (N ω).toReal ∂P) = r)
    (hSecond : Integrable
        (fun ω => (N ω).toReal * ((N ω).toReal - 1)) P ∧
      (∫ ω, (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2) :
    r - r ^ 2 / 2 ≤ 1 - (P {ω | N ω = 0}).toReal ∧
      1 - (P {ω | N ω = 0}).toReal ≤ r := by
  have hI : Integrable (fun ω => (K ω : ℝ)) P := by
    apply hFirst.1.congr
    filter_upwards [hCount] with ω hc
    exact hc.symm
  have hJ : Integrable (fun ω => (K ω : ℝ) *
      ((K ω : ℝ) - 1)) P := by
    apply hSecond.1.congr
    filter_upwards [hCount] with ω hc
    simp [hc]
  have hMom :=
    avram_a25_integrated_nat_count_occupancy_factorial_sandwich_20261115
      P K hK hI hJ
  have hEvent : {ω | N ω = 0} =ᵐ[P] {ω | K ω = 0} := by
    filter_upwards [hCount, hFin] with ω hc hf
    apply propext
    constructor
    · intro hz
      have hzR : (N ω).toReal = 0 :=
        (congrArg ENNReal.toReal hz).trans ENNReal.toReal_zero
      have hkR : (K ω : ℝ) = 0 := hc.trans hzR
      exact_mod_cast hkR
    · intro hk
      have hkR : (K ω : ℝ) = 0 := by exact_mod_cast hk
      have hz : (N ω).toReal = 0 := hc.symm.trans hkR
      rcases (ENNReal.toReal_eq_zero_iff (N ω)).mp hz with hz | hz
      · exact hz
      · exact False.elim ((ne_top_of_lt hf) hz)
  have hZero : MeasurableSet {ω | K ω = 0} :=
    hK (measurableSet_singleton 0)
  have hProb : (P {ω | K ω ≠ 0}).toReal =
      1 - (P {ω | N ω = 0}).toReal := by
    change P.real {ω | K ω ≠ 0} = 1 - P.real {ω | N ω = 0}
    have hc : {ω | K ω ≠ 0} = {ω | K ω = 0}ᶜ := by
      ext ω
      simp
    rw [hc, probReal_compl_eq_one_sub hZero, measureReal_congr hEvent.symm]
  have hFirstMean : (∫ ω, (K ω : ℝ) ∂P) = r := by
    rw [integral_congr_ae hCount]
    exact hFirst.2
  have hSecEq :
      (fun ω : Ω => (K ω : ℝ) * ((K ω : ℝ) - 1)) =ᵐ[P]
        (fun ω => (N ω).toReal * ((N ω).toReal - 1)) := by
    filter_upwards [hCount] with ω hc
    simp [hc]
  have hSecondMean : (∫ ω, (K ω : ℝ) *
      ((K ω : ℝ) - 1) ∂P) = r ^ 2 := by
    rw [integral_congr_ae hSecEq]
    exact hSecond.2
  simpa only [hFirstMean, hSecondMean, hProb] using hMom
