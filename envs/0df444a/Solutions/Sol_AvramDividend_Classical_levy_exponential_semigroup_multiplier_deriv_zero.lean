-- Prove2me | solution 1 for AvramDividend.Classical.levy_exponential_semigroup_multiplier_deriv_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T22:17:28.390756+00:00
-- url     : https://prove2.me/submissions/50297f72-0398-4a78-8781-778115ac9d30

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ x : ℝ) :
    HasDerivAt
      (fun h : ℝ =>
        Real.exp (θ * x) *
          Real.exp (h * laplaceExponent X.c X.σ X.ν θ))
      (Real.exp (θ * x) * laplaceExponent X.c X.σ X.ν θ)
      0 := by
  let ψ := laplaceExponent X.c X.σ X.ν θ
  have hbase :=
    (((hasDerivAt_id (0 : ℝ)).mul_const ψ).exp).const_mul
      (Real.exp (θ * x))
  simpa [ψ, id_eq, mul_assoc, mul_comm, mul_left_comm] using hbase
