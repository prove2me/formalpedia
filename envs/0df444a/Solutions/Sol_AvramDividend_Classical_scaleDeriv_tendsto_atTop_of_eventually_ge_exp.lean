-- Prove2me | solution 1 for AvramDividend.Classical.scaleDeriv_tendsto_atTop_of_eventually_ge_exp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-03T11:56:39.296896+00:00
-- url     : https://prove2.me/submissions/e63464f1-ce74-49dd-af36-65de3ab7a2d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hexp : ∃ φ c : ℝ, 0 < φ ∧ 0 < c ∧
      ∀ᶠ x in Filter.atTop, c * Real.exp (φ * x) ≤ deriv W x) :
    Tendsto (deriv W) Filter.atTop Filter.atTop := by
  obtain ⟨φ, c, hφ, hc, hbound⟩ := hexp
  have hlin : Tendsto (fun x : ℝ => φ * x) Filter.atTop Filter.atTop :=
    tendsto_id.const_mul_atTop hφ
  have hdiv :
      Tendsto (fun x : ℝ => c * Real.exp (φ * x)) Filter.atTop Filter.atTop :=
    (Real.tendsto_exp_atTop.comp hlin).const_mul_atTop hc
  exact tendsto_atTop_mono' Filter.atTop hbound hdiv
