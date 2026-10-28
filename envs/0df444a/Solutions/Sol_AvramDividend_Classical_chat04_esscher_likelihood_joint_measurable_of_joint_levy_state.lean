-- Prove2me | solution 1 for AvramDividend.Classical.chat04_esscher_likelihood_joint_measurable_of_joint_levy_state
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-27T10:36:27.43056+00:00
-- url     : https://prove2.me/submissions/b05c168d-1af1-4171-8035-6454df6bd181

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ)
    (hJoint : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2)) :
    Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))) := by
  have ht : Measurable (fun z : Ω × ℝ => Real.toNNReal z.2) :=
    measurable_real_toNNReal.comp measurable_snd
  have htime : Measurable (fun z : Ω × ℝ => (Real.toNNReal z.2 : ℝ)) :=
    measurable_coe_nnreal_real.comp ht
  have hstate : Measurable
      (fun z : Ω × ℝ => X.X (Real.toNNReal z.2) z.1) :=
    hJoint.comp (ht.prodMk measurable_fst)
  exact ((hstate.const_mul θ).sub (htime.mul_const (X.ψ θ))).exp.ennreal_ofReal
