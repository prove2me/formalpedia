-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_generator_congr_scaledW_inside_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T14:08:42.984458+00:00
-- url     : https://prove2.me/submissions/69f68ae7-abcf-4bee-bad7-d82bc22043e8

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar_of_support
import Theorems.Thm_AvramDividend_Classical_generator_boundary_left_germ_congr
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
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hx : x ∈ Ioo 0 (cstar W).toReal) :
    (X.GeneratorIntegrable (vcstar W) x ↔
      X.GeneratorIntegrable
        (fun z : ℝ => divE (W z)
          (scaleDeriv W (cstar W).toReal)) x) ∧
      X.generator (vcstar W) x =
        X.generator (fun z : ℝ => divE (W z)
          (scaleDeriv W (cstar W).toReal)) x := by
  let g : ℝ → ℝ :=
    fun z => divE (W z) (scaleDeriv W (cstar W).toReal)
  have hbelow : ∀ z : ℝ, z ≤ (cstar W).toReal →
      vcstar W z = g z := by
    intro z hz
    exact vcstar_eq_scaledW_le_cstar_of_support W hW.1 z hz
  have hopen : EqOn (vcstar W) g (Iio (cstar W).toReal) := by
    intro z hz
    exact hbelow z (le_of_lt hz)
  have hleft : ∀ z : ℝ, z ≤ x → vcstar W z = g z := by
    intro z hz
    exact hbelow z (le_trans hz (le_of_lt hx.2))
  have hder : deriv (vcstar W) x = deriv g x :=
    (hopen.deriv isOpen_Iio) hx.2
  have hsecond : iteratedDeriv 2 (vcstar W) x =
      iteratedDeriv 2 g x :=
    (hopen.iteratedDeriv_of_isOpen isOpen_Iio 2) hx.2
  exact generator_boundary_left_germ_congr X
    (vcstar W) g x hleft hder hsecond
