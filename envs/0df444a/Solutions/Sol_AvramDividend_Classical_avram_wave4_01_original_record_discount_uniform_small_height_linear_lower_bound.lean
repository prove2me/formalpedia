-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_record_discount_uniform_small_height_linear_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T15:39:20.901918+00:00
-- url     : https://prove2.me/submissions/7421b056-dd99-4301-88df-81b445556bdf

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_unbounded_scale_logderiv_antitone_without_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_record_discount_exp_log_scale_deriv
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- One source-height Lipschitz envelope works uniformly above any positive drawdown depth cutoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : ∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν = ⊤)
    (δ a h : ℝ) (hδ : 0 < δ) (hδa : δ ≤ a) (hh : 0 < h) :
    1 - h * (deriv W δ / W δ) ≤
      (∫⁻ ω, if twoSidedExitUpTime X h ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitUpTime X h ω).toReal)))
      else 0 ∂P).toReal := by
  have ha : 0 < a := lt_of_lt_of_le hδ hδa
  have hnbv : ¬ X.BoundedVariation :=
    avram_wave3_01_infinite_small_jump_not_bv X hvar
  have hanti : AntitoneOn
      (fun x : ℝ => deriv W x / W x) (Ioi (0 : ℝ)) :=
    avram_wave4_01_unbounded_scale_logderiv_antitone_without_standing
      X q hq W hW hnbv
  have hK : deriv W a / W a ≤ deriv W δ / W δ :=
    hanti hδ ha hδa
  have hlin : 1 - h * (deriv W δ / W δ) ≤
      1 - h * (deriv W a / W a) := by
    have hm := mul_le_mul_of_nonneg_left hK (le_of_lt hh)
    linarith
  have htan := Real.add_one_le_exp (-(h * (deriv W a / W a)))
  have hE := avram_wave4_01_original_record_discount_exp_log_scale_deriv
    X q hq W hW hvar a h ha hh
  rw [hE]
  linarith
