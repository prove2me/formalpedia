-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_measure_atom_transform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T07:04:24.886421+00:00
-- url     : https://prove2.me/submissions/69122702-ee2b-4cb2-80a6-01a23c65eb1e

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_atom_esscher_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Integrate the Esscher-weighted Gaussian atom identity against the jump measure. -/
theorem solution
    (μ : Measure ℝ) [SFinite μ] (φ θ : ℝ)
    (hφ : 0 < φ) (hθ : 0 ≤ θ) :
    ENNReal.ofReal (θ ^ 2) *
      (∫⁻ z : ℝ, ∫⁻ t : ℝ,
        (if 0 < t ∧ t < z then
          ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
            ENNReal.ofReal (Real.exp (-φ * z))
         else 0) ∂volume ∂μ) =
      (∫⁻ z in Ioi (0 : ℝ),
        ENNReal.ofReal
          (Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z)) ∂μ) := by
  let K : ℝ → ℝ → ENNReal := fun t z =>
    if 0 < t ∧ t < z then
      ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
        ENNReal.ofReal (Real.exp (-φ * z))
    else 0
  have hs : MeasurableSet {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < p.2} := by
    exact (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_snd)
  have hk : Measurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal ((p.2 - p.1) * Real.exp (-θ * p.1)) *
        ENNReal.ofReal (Real.exp (-φ * p.2))) := by
    fun_prop
  have hK : Measurable (fun p : ℝ × ℝ => K p.1 p.2) := by
    exact hk.ite hs measurable_const
  have houter : Measurable (fun z : ℝ =>
      ∫⁻ t : ℝ, K t z ∂volume) :=
    hK.lintegral_prod_left
  have hpoint (z : ℝ) :
      ENNReal.ofReal (θ ^ 2) * (∫⁻ t : ℝ, K t z ∂volume) =
        if 0 < z then
          ENNReal.ofReal
            (Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z))
        else 0 := by
    by_cases hz : 0 < z
    · have hfun :
          (fun t : ℝ => K t z) =
            (Ioo (0 : ℝ) z).indicator
              (fun t => ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
                ENNReal.ofReal (Real.exp (-φ * z))) := by
        funext t
        dsimp [K]
        simp [Set.indicator, Set.mem_Ioo]
      have hinner :
          (∫⁻ t : ℝ, K t z ∂volume) =
            (∫⁻ t in Ioo (0 : ℝ) z,
              ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
                ENNReal.ofReal (Real.exp (-φ * z)) ∂volume) := by
        rw [hfun]
        exact lintegral_indicator measurableSet_Ioo _
      rw [if_pos hz, hinner]
      have hmeas : Measurable (fun t : ℝ =>
          ENNReal.ofReal ((z - t) * Real.exp (-θ * t)) *
            ENNReal.ofReal (Real.exp (-φ * z))) := by
        fun_prop
      rw [← lintegral_const_mul (ENNReal.ofReal (θ ^ 2)) hmeas]
      simpa only [mul_assoc] using
        AvramDividend.Classical.gaussian_double_tail_atom_esscher_lintegral
          φ θ z hφ hθ hz.le
    · have hzero : ∀ t : ℝ, K t z = 0 := by
        intro t
        have hbad : ¬ (0 < t ∧ t < z) := by
          rintro ⟨ht, htz⟩
          linarith
        simp [K, hbad]
      simp only [if_neg hz]
      simp_rw [hzero]
      simp
  change ENNReal.ofReal (θ ^ 2) *
    (∫⁻ z : ℝ, ∫⁻ t : ℝ, K t z ∂volume ∂μ) = _
  calc
    ENNReal.ofReal (θ ^ 2) *
        (∫⁻ z : ℝ, ∫⁻ t : ℝ, K t z ∂volume ∂μ) =
      (∫⁻ z : ℝ,
        ENNReal.ofReal (θ ^ 2) *
          (∫⁻ t : ℝ, K t z ∂volume) ∂μ) :=
      (lintegral_const_mul (ENNReal.ofReal (θ ^ 2)) houter).symm
    _ = (∫⁻ z : ℝ,
        if 0 < z then
          ENNReal.ofReal
            (Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z))
        else 0 ∂μ) := by
      apply lintegral_congr
      intro z
      exact hpoint z
    _ = (∫⁻ z in Ioi (0 : ℝ),
        ENNReal.ofReal
          (Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z)) ∂μ) := by
      have hfun :
          (fun z : ℝ =>
            if 0 < z then
              ENNReal.ofReal
                (Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z))
            else 0) =
            (Ioi (0 : ℝ)).indicator
              (fun z => ENNReal.ofReal
                (Real.exp (-φ * z) * (Real.exp (-θ * z) - 1 + θ * z))) := by
        funext z
        simp [Set.indicator, Set.mem_Ioi]
      rw [hfun]
      exact lintegral_indicator measurableSet_Ioi _
