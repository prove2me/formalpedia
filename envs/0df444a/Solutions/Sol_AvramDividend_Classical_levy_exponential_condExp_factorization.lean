-- Prove2me | solution 1 for AvramDividend.Classical.levy_exponential_condExp_factorization
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T12:38:39.908707+00:00
-- url     : https://prove2.me/submissions/c1ed585d-bf7c-4baf-8a44-c02a5df84aab

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_Borel_payoff

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
    (s t : ℝ≥0) (hst : s ≤ t) (θ : ℝ)
    (hPast : StronglyMeasurable[𝓕 s]
      (fun ω => Real.exp (θ * X.X s ω)))
    (hTotal : Integrable (fun ω => Real.exp (θ * X.X t ω)) P)
    (hIncrement : Integrable
      (fun ω => Real.exp (θ * (X.X t ω - X.X s ω))) P)
    (hDet : Integrable
      (fun ω => Real.exp (θ * X.X (t - s) ω)) P) :
    P[(fun ω => Real.exp (θ * X.X t ω)) | 𝓕 s] =ᵐ[P]
      (fun ω => Real.exp (θ * X.X s ω) *
        (∫ η, Real.exp (θ * X.X (t - s) η) ∂P)) := by
  let U : Ω → ℝ := fun ω => Real.exp (θ * X.X s ω)
  let V : Ω → ℝ := fun ω =>
    Real.exp (θ * (X.X t ω - X.X s ω))
  have hFactor : U * V = (fun ω => Real.exp (θ * X.X t ω)) := by
    funext ω
    change Real.exp (θ * X.X s ω) *
        Real.exp (θ * (X.X t ω - X.X s ω)) =
      Real.exp (θ * X.X t ω)
    rw [← Real.exp_add]
    congr 1
    ring
  have hProd : Integrable (U * V) P := by
    rw [hFactor]
    exact hTotal
  have hPull :=
    condExp_mul_of_stronglyMeasurable_left hPast hProd hIncrement
  have hM : Measurable (fun z : ℝ => Real.exp (θ * z)) :=
    (Real.continuous_exp.comp
      (continuous_const.mul continuous_id)).measurable
  have hI : Integrable
      (fun ω => Real.exp (θ * ((0 : ℝ) + X.X (t - s) ω))) P := by
    simpa only [zero_add] using hDet
  have hCE :
      (P[V | 𝓕 s]) =ᵐ[P]
        (fun _ => ∫ η, Real.exp (θ * X.X (t - s) η) ∂P) := by
    simpa only [zero_add] using
      (levy_increment_condExp_Borel_payoff
        X s t hst 0 (fun z => Real.exp (θ * z)) hM hI)
  filter_upwards [hPull, hCE] with ω hp hc
  calc
    (P[(fun η => Real.exp (θ * X.X t η)) | 𝓕 s]) ω =
        (P[U * V | 𝓕 s]) ω := by simp only [hFactor]
    _ = U ω * (P[V | 𝓕 s]) ω := by
      simpa only [Pi.mul_apply] using hp
    _ = U ω * (∫ η, Real.exp (θ * X.X (t - s) η) ∂P) := by
      rw [hc]
