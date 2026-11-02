-- Prove2me | solution 3 for AvramDividend.Classical.scaleFunction_generator_eq_q_of_integrable_nonzero_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:13:44.140201+00:00
-- url     : https://prove2.me/submissions/7efc49c8-0267-4b83-b7a6-d2f8c2344774

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaled_scaleFunction_q_harmonic_below_cstar
import Theorems.Thm_AvramDividend_Classical_levy_generator_const_mul

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0)
    (hint : ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.generator W x - q * W x = 0 := by
  intro x hx
  let a : EReal := scaleDeriv W (cstar W).toReal
  let k : ℝ := divE (1 : ℝ) a
  have ha : a ≠ ⊤ := by
    intro heq
    apply hk
    change divE (1 : ℝ) a = 0
    simp [divE, heq]
  have hdiv (z : ℝ) : divE (W z) a = k * W z := by
    change divE (W z) a = divE (1 : ℝ) a * W z
    simp [divE, ha, div_eq_mul_inv, mul_comm]
  have hfun :
      (fun z : ℝ => divE (W z) a) =
      (fun z : ℝ => k * W z) := funext hdiv
  have hs :=
    (scaled_scaleFunction_q_harmonic_below_cstar
      X hX q hq W hW h_smooth hc x hx).2
  change X.generator (fun z : ℝ => divE (W z) a) x -
    q * divE (W x) a = 0 at hs
  rw [hfun, hdiv x, levy_generator_const_mul X W k x] at hs
  have hmul : k * (X.generator W x - q * W x) = 0 := by
    calc
      k * (X.generator W x - q * W x) =
          k * X.generator W x - q * (k * W x) := by ring
      _ = 0 := hs
  exact (mul_eq_zero.mp hmul).resolve_left hk
