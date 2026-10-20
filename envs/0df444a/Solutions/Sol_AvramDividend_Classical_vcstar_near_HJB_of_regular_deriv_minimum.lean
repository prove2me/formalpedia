-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_near_HJB_of_regular_deriv_minimum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:51:55.297664+00:00
-- url     : https://prove2.me/submissions/51d7f1b7-730d-405e-b880-c1ae2ec92fbc

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_regular_minimal
import Theorems.Thm_AvramDividend_Classical_vcstar_near_HJB_of_affine_majorant_at_threshold
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hreg : ContDiffOn ℝ 1 W (Ioi 0))
    (hpositive : ∀ z : ℝ, 0 < z → 0 < deriv W z)
    (a : ℝ) (ha : a = (cstar W).toReal) (hapos : 0 < a)
    (hminimal : ∀ z : ℝ, 0 < z → deriv W a ≤ deriv W z)
    (hcont : ContinuousOn (vcstar W) (Icc 0 a))
    (x : ℝ) (hx : a < x) (hx1 : 1 ≤ x)
    (hthreshold : a + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by
  have hmin : (cstar W).toReal = 0 ∨
      (0 < (cstar W).toReal ∧
        ∀ z : ℝ, 0 < z →
          deriv W (cstar W).toReal ≤ deriv W z) := by
    right
    constructor
    · rw [← ha]
      exact hapos
    · simpa only [← ha] using hminimal
  have hderiv :=
    vcstar_deriv_ge_one_of_regular_minimal W hreg hpositive hmin
  have hdiff : ∀ z ∈ Ioo (0 : ℝ) a,
      DifferentiableAt ℝ (vcstar W) z := by
    intro z hz
    exact (hderiv z hz.1).1
  have hder : ∀ z ∈ Ioo (0 : ℝ) a,
      1 ≤ deriv (vcstar W) z := by
    intro z hz
    exact (hderiv z hz.1).2
  have hcontg : ContinuousOn ((vcstar W) - id) (Icc 0 a) :=
    hcont.sub continuousOn_id
  have hdiffg : DifferentiableOn ℝ
      ((vcstar W) - id) (interior (Icc 0 a)) := by
    rw [interior_Icc]
    intro z hz
    exact (hdiff z hz).differentiableWithinAt.sub
      differentiableWithinAt_id
  have hderg : ∀ z ∈ interior (Icc (0 : ℝ) a),
      0 ≤ deriv ((vcstar W) - id) z := by
    intro z hz
    have hzi : z ∈ Ioo (0 : ℝ) a := by
      simpa only [interior_Icc] using hz
    have hcalc : deriv ((vcstar W) - id) z =
        deriv (vcstar W) z - deriv (id : ℝ → ℝ) z :=
      deriv_sub (hdiff z hzi) differentiableAt_id
    rw [hcalc, deriv_id]
    linarith [hder z hzi]
  have hgmono : MonotoneOn ((vcstar W) - id) (Icc 0 a) :=
    monotoneOn_of_deriv_nonneg
      (convex_Icc (0 : ℝ) a) hcontg hdiffg hderg
  have hchord : ∀ z : ℝ, 0 ≤ z → z ≤ (cstar W).toReal →
      vcstar W z ≤ z - (cstar W).toReal +
        vcstar W (cstar W).toReal := by
    intro z hz0 hzle
    have hzlea : z ≤ a := by simpa only [← ha] using hzle
    have hz : z ∈ Icc (0 : ℝ) a := ⟨hz0, hzlea⟩
    have haa : a ∈ Icc (0 : ℝ) a :=
      ⟨le_of_lt hapos, le_rfl⟩
    have hm := hgmono hz haa hzlea
    change vcstar W z - z ≤ vcstar W a - a at hm
    rw [← ha]
    linarith
  have hx' : (cstar W).toReal < x := by simpa only [← ha] using hx
  have hp' : 0 < (cstar W).toReal := by simpa only [← ha] using hapos
  have ht' : (cstar W).toReal + max 0 (X.c / q) ≤ x := by
    simpa only [← ha] using hthreshold
  exact vcstar_near_HJB_of_affine_majorant_at_threshold
    X q hq W hW hp' hchord x hx' hx1 ht'
