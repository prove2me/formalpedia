-- Prove2me | solution 1 for AvramDividend.Classical.barrier_cstar_optimal_of_finiteness_attainment_verification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T11:19:10.426484+00:00
-- url     : https://prove2.me/submissions/0dac0ab9-d2a9-4609-8ec3-b1a07756366f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_valueFunctionLe_eq_of_attainment_and_upper_bound
import Theorems.Thm_AvramDividend_Classical_valueFunction_eq_of_attainment_and_upper_bound
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hc : cstar W < ⊤)
    (hattain : ∀ x : ℝ, 0 ≤ x →
      IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
        dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
          ENNReal.ofReal (vcstar W x))
    (hverify : (∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) ∧
    ((∀ y : ℝ, (cstar W).toReal < y →
       X.GeneratorIntegrable (vcstar W) y ∧
         X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
      ∀ x : ℝ, 0 ≤ x →
        valueFunction X q x ≤ ENNReal.ofReal (vcstar W x))) :
    cstar W < ⊤ ∧
      (∀ x : ℝ, 0 ≤ x →
        IsAdmissibleLe X x (cstar W) (barrierStrategy X x (cstar W).toReal) ∧
          dividendValue X q x (barrierStrategy X x (cstar W).toReal) =
            ENNReal.ofReal (vcstar W x) ∧
          valueFunctionLe X q (cstar W) x = ENNReal.ofReal (vcstar W x)) ∧
      ((∀ x : ℝ, (cstar W).toReal < x →
          X.GeneratorIntegrable (vcstar W) x ∧ X.generator (vcstar W) x - q * vcstar W x ≤ 0) →
        ∀ x : ℝ, 0 ≤ x →
          IsAdmissible X x (barrierStrategy X x (cstar W).toReal) ∧
            valueFunction X q x = ENNReal.ofReal (vcstar W x)) := by
  refine And.intro hc (And.intro ?_ ?_)
  · intro x hx
    have hadm := (hattain x hx).1
    have hvalue := (hattain x hx).2
    refine And.intro hadm (And.intro hvalue ?_)
    exact valueFunctionLe_eq_of_attainment_and_upper_bound X q x (cstar W)
      (ENNReal.ofReal (vcstar W x)) (barrierStrategy X x (cstar W).toReal)
      hadm hvalue (hverify.1 x hx)
  · intro hgen x hx
    have hadm := (hattain x hx).1
    have hvalue := (hattain x hx).2
    refine And.intro hadm.1 ?_
    exact valueFunction_eq_of_attainment_and_upper_bound X q x
      (ENNReal.ofReal (vcstar W x)) (barrierStrategy X x (cstar W).toReal)
      hadm.1 hvalue (hverify.2 hgen x hx)
