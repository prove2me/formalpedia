-- Prove2me | solution 2 for AvramDividend.Classical.scaled_scaleFunction_q_harmonic_below_cstar
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T19:28:44.358988+00:00
-- url     : https://prove2.me/submissions/abed3752-ac69-46d3-9dfa-e27885a3e83e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_const_mul_of_integrable
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-! Constant-scaling reduction of q-harmonicity, including vanishing normalisers. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable
          (fun z => divE (W z) (scaleDeriv W (cstar W).toReal)) x ∧
        X.generator
            (fun z => divE (W z) (scaleDeriv W (cstar W).toReal)) x -
          q * divE (W x) (scaleDeriv W (cstar W).toReal) = 0 := by
  let k : ℝ := divE (1 : ℝ) (scaleDeriv W (cstar W).toReal)
  have hfactor (z : ℝ) :
      divE (W z) (scaleDeriv W (cstar W).toReal) = k * W z := by
    dsimp [k]
    by_cases htop : scaleDeriv W (cstar W).toReal = ⊤
    · simp [divE, htop]
    · simp [divE, htop, div_eq_mul_inv, mul_comm]
  have hfun :
      (fun z => divE (W z) (scaleDeriv W (cstar W).toReal)) =
      (fun z => k * W z) := funext hfactor
  intro x hx
  rw [hfun, hfactor x]
  by_cases hk : k = 0
  · have hzfun : (fun z => k * W z) = (fun _ : ℝ => (0 : ℝ)) := by
      funext z
      simp [hk]
    rw [hzfun]
    constructor
    · change IntegrableOn
        (SpectrallyNegativeLevy.generatorIntegrand
          (fun _ : ℝ => (0 : ℝ)) x)
        (Iio (0 : ℝ)) X.ν
      have hzero_integrand :
          SpectrallyNegativeLevy.generatorIntegrand
              (fun _ : ℝ => (0 : ℝ)) x =
            (fun _ : ℝ => (0 : ℝ)) := by
        funext y
        simp [SpectrallyNegativeLevy.generatorIntegrand]
      rw [hzero_integrand]
      exact integrableOn_zero
    · simp [SpectrallyNegativeLevy.generator,
        SpectrallyNegativeLevy.generatorIntegrand, hk]
  · have hbase :=
      scaleFunction_generator_q_harmonic_of_nonzero_factor
        X hX q hq W hW h_smooth hc hk x hx
    obtain ⟨hscaled, hgen⟩ :=
      generator_const_mul_of_integrable X W x k hbase.1
    constructor
    · exact hscaled
    · rw [hgen, sub_eq_zero.mp hbase.2]
      ring
