-- Prove2me | solution 1 for AvramDividend.Classical.generator_vcstar_eq_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T23:13:31.627981+00:00
-- url     : https://prove2.me/submissions/75dcb8a4-15d3-433c-b551-946f3f136375
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_eq_of_agree_below
import Theorems.Thm_AvramDividend_Classical_scaled_scaleFunction_q_harmonic_below_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Lemma 4 reduction: on the open region below c*, the barrier value
agrees with the scaled q-scale function on every lower capital level.
The spectrally negative generator is local on the entire downward ray,
so the scaled function's q-harmonicity transfers to the barrier value.
Both imported lemmas are source-faithful analytic obligations.
-/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x - q * vcstar W x = 0 := by
  intro x hx
  have hagree :
      ∀ z : ℝ, z < (cstar W).toReal →
        vcstar W z =
          divE (W z) (scaleDeriv W (cstar W).toReal) := by
    intro z hza
    change barrierValue W (cstar W).toReal z =
      divE (W z) (scaleDeriv W (cstar W).toReal)
    by_cases hz : z < 0
    · simp [barrierValue, hz, hW.1 z hz, divE]
    · have hle : z ≤ (cstar W).toReal := le_of_lt hza
      simp [barrierValue, hz, hle]
  have hscale :=
    scaled_scaleFunction_q_harmonic_below_cstar
      X hX q hq W hW h_smooth hc x hx
  have hlocal :=
    generator_eq_of_agree_below X (vcstar W)
      (fun z => divE (W z) (scaleDeriv W (cstar W).toReal))
      (cstar W).toReal x hx.2 hagree
  constructor
  · exact hlocal.1.mpr hscale.1
  · rw [hlocal.2, hagree x hx.2]
    exact hscale.2
