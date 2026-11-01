-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_05_source_positive_jump_kernel_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:41:31.078435+00:00
-- url     : https://prove2.me/submissions/98ae0add-cc6b-4b24-9bc7-0f75c374e06c

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_vcstar_continuousOn_Icc_below_positive_cstar
import Theorems.Thm_AvramDividend_Classical_left_affine_majorant_of_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_monotone_of_finite_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar
import Theorems.Thm_AvramDividend_Classical_barrier_generatorIntegrand_zero_small_negative_jump_above
import Mathlib.Analysis.Calculus.FDeriv.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Positive compensated generator mass can only come from small jumps
which cross reserve zero; all other negative jumps have nonpositive kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hpos : 0 < (cstar W).toReal)
    (x : ℝ) (hx : (cstar W).toReal < x)
    (y : ℝ) (hy : y < 0)
    (houtside : y ∉ Ioo (-1 : ℝ) (-x)) :
    SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y ≤ 0 := by
  let a : ℝ := (cstar W).toReal
  have ha : 0 ≤ a := le_of_lt hpos
  have hcont : ContinuousOn (vcstar W) (Icc 0 a) :=
    vcstar_continuousOn_Icc_below_positive_cstar X q W hW hpos
  have hdiff : ∀ z ∈ Ioo (0 : ℝ) a,
      DifferentiableAt ℝ (vcstar W) z := by
    intro z hz
    exact (vcstar_deriv_ge_one X hX q hq W hW z hz.1).1
  have hder0 : ∀ z ∈ Ioo (0 : ℝ) a,
      1 ≤ deriv (vcstar W) z := by
    intro z hz
    exact (vcstar_deriv_ge_one X hX q hq W hW z hz.1).2
  have hchord := left_affine_majorant_of_deriv_ge_one
    (vcstar W) a ha hcont hdiff hder0
  have hcfin : cstar W < ⊤ := cstar_lt_top X hX q hq W hW
  have hmono : Monotone (vcstar W) :=
    vcstar_monotone_of_finite_cstar X hX q hq W hW hcfin
  have hvalx : vcstar W x = x - a + vcstar W a := by
    have hx0 : ¬ x < 0 := not_lt.mpr (le_trans ha (le_of_lt hx))
    have hxa : ¬ x ≤ a := not_le.mpr hx
    have ha0 : ¬ a < 0 := not_lt.mpr ha
    change barrierValue W a x = x - a + barrierValue W a a
    simp only [barrierValue, if_neg hx0, if_neg hxa,
      if_neg ha0, if_pos le_rfl]
  have hder : deriv (vcstar W) x = 1 :=
    vcstar_deriv_eq_one_above_cstar W x hx
  by_cases hlarge : y ≤ -1
  · have hnot : y ∉ Ioo (-1 : ℝ) 1 := by
      intro hmem
      exact (not_lt_of_ge hlarge) hmem.1
    have hxy : x + y ≤ x := by linarith
    have hm := hmono hxy
    unfold SpectrallyNegativeLevy.generatorIntegrand
    simp [Set.indicator_of_notMem hnot]
    linarith
  · have hy1 : -1 < y := lt_of_not_ge hlarge
    have hmem : y ∈ Ioo (-1 : ℝ) 1 := ⟨hy1, by linarith⟩
    by_cases hruin : x + y < 0
    · have hbad : y ∈ Ioo (-1 : ℝ) (-x) := ⟨hy1, by linarith⟩
      exact False.elim (houtside hbad)
    · have hz0 : 0 ≤ x + y := le_of_not_gt hruin
      by_cases hbelow : x + y ≤ a
      · have hb := hchord (x + y) hz0 hbelow
        unfold SpectrallyNegativeLevy.generatorIntegrand
        simp only [Set.indicator_of_mem hmem, Pi.one_apply]
        rw [hvalx, hder]
        simp only [one_mul, mul_one]
        linarith
      · have hz : a < x + y := lt_of_not_ge hbelow
        have hzero :
            SpectrallyNegativeLevy.generatorIntegrand (vcstar W) x y = 0 := by
          change SpectrallyNegativeLevy.generatorIntegrand
            (barrierValue W a) x y = 0
          exact barrier_generatorIntegrand_zero_small_negative_jump_above
            W a x y ha hx hz hy1 hy
        exact le_of_eq hzero
