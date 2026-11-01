-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_zero_cap_positive_jump_kernel_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T17:27:53.559989+00:00
-- url     : https://prove2.me/submissions/66878a65-44da-447a-87ae-d80633353e0d

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_zero_cstar
import Theorems.Thm_AvramDividend_Classical_barrierValue_zero_affine_nonnegative
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
import Mathlib.Algebra.Notation.Indicator
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- At the source zero optimal cap, the compensated jump kernel is
nonpositive outside the strict small-ruin crossing strip. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc0 : cstar W = 0)
    (x : ℝ) (hx : 0 < x)
    (y : ℝ) (hy : y < 0)
    (houtside : y ∉ Ioo (-1 : ℝ) (-x)) :
    SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ≤ 0 := by
  have hmono : Monotone (vcstar W) :=
    vcstar_monotone_of_zero_cstar X hX q hq W hW hc0
  have hder : deriv (vcstar W) x = 1 :=
    vcstar_deriv_eq_one_above_cstar W x (by simpa [hc0] using hx)
  by_cases hlarge : y ≤ -1
  · have hnot : y ∉ Ioo (-1 : ℝ) 1 := by
      intro hmem
      exact (not_lt_of_ge hlarge) hmem.1
    have hxy : x + y ≤ x := by linarith
    have hm : vcstar W (x + y) ≤ vcstar W x := hmono hxy
    unfold SpectrallyNegativeLevy.generatorIntegrand
    simp [Set.indicator_of_notMem hnot]
    linarith
  · have hy1 : -1 < y := lt_of_not_ge hlarge
    have hmem : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy1, by linarith⟩
    by_cases hruin : x + y < 0
    · have hbad : y ∈ Ioo (-1 : ℝ) (-x) := ⟨hy1, by linarith⟩
      exact False.elim (houtside hbad)
    · have hxy0 : 0 ≤ x + y := le_of_not_gt hruin
      have hvx : vcstar W x = x + vcstar W 0 := by
        change barrierValue W (cstar W).toReal x =
          x + barrierValue W (cstar W).toReal 0
        simpa [hc0] using barrierValue_zero_affine_nonnegative W x (le_of_lt hx)
      have hvxy : vcstar W (x + y) = x + y + vcstar W 0 := by
        change barrierValue W (cstar W).toReal (x + y) =
          x + y + barrierValue W (cstar W).toReal 0
        simpa [hc0] using barrierValue_zero_affine_nonnegative W (x + y) hxy0
      unfold SpectrallyNegativeLevy.generatorIntegrand
      simp only [Set.indicator_of_mem hmem, Pi.one_apply]
      rw [hvxy, hvx, hder]
      simp only [mul_one]
      linarith
