-- Prove2me | solution 1 for AvramDividend.Classical.levy_compensated_exponential_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:28:34.116982+00:00
-- url     : https://prove2.me/submissions/821e1478-37ee-437a-befb-4b8a329e5fbf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    Integrable (fun ω => Real.exp
      (θ * X.X t ω - (t : ℝ) * X.ψ θ)) P := by
  let a : ℝ := (t : ℝ) * X.ψ θ
  have hLap : Integrable (fun ω => Real.exp (θ * X.X t ω)) P :=
    (X.laplace t θ hθ).1
  have heq :
      (fun ω => Real.exp (θ * X.X t ω - a)) =
      (fun ω => Real.exp (θ * X.X t ω) * Real.exp (-a)) := by
    funext ω
    rw [sub_eq_add_neg, Real.exp_add]
  change Integrable (fun ω => Real.exp (θ * X.X t ω - a)) P
  rw [heq]
  exact hLap.mul_const _
