-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p2_scale_primitive_generatorIntegrand_interior_taylor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:54:29.131362+00:00
-- url     : https://prove2.me/submissions/0044d130-9cca-45f4-99ed-a0fab3205639

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p2_scale_primitive_contDiffOn_two_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave3_05_positive_C2_backward_taylor_exact
import Theorems.Thm_AvramDividend_Classical_generatorIntegrand_negative_jump_reflection

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

/-- Exact interior second-order remainder for the genuine scale primitive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (r x : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (hrx : r < x) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun z : ℝ => ∫ s in (0 : ℝ)..z, W s) x (-r) =
      ∫ t in (x-r)..x, (t - (x-r)) *
        iteratedDeriv 2 (fun z : ℝ => ∫ s in (0 : ℝ)..z, W s) t := by
  let U : ℝ → ℝ := fun z => ∫ s in (0 : ℝ)..z, W s
  have hC2 : ContDiffOn ℝ 2 U (Ioi (0 : ℝ)) :=
    avram_wave4_p2_scale_primitive_contDiffOn_two_of_standing
      X hX q hq W hW
  have hTaylor :=
    avram_wave3_05_positive_C2_backward_taylor_exact
      U hC2 (x-r) x (by linarith) (by linarith)
  have hy : -r < 0 := by linarith
  calc
    SpectrallyNegativeLevy.generatorIntegrand U x (-r) =
      U (x - (-(-r))) - U x +
        (if -(-r) < 1 then (-(-r)) * deriv U x else 0) :=
      (generatorIntegrand_negative_jump_reflection U x (-r) hy).symm
    _ = U (x-r) - U x + (x-(x-r)) * deriv U x := by
      simp only [neg_neg, if_pos hr1]
      ring
    _ = ∫ t in (x-r)..x, (t-(x-r)) * iteratedDeriv 2 U t := hTaylor
