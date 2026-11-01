-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_negative_levy_measure_sigmaFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T22:11:40.035722+00:00
-- url     : https://prove2.me/submissions/a6509864-49bd-440a-8b15-dde090cebaa2

import Mathlib.MeasureTheory.Measure.Typeclasses.SFinite
import Theorems.Thm_AvramDividend_Classical_gaussian_negative_jump_pushforward_sigmaFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Negative Lévy square-integrability implies sigma-finiteness of the
original signed-mark measure, not merely its magnitude pushforward. -/
theorem solution
    (ν : Measure ℝ)
    (hν : ν (Ici (0 : ℝ)) = 0)
    (hlevy : (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    SigmaFinite ν := by
  have hpush : SigmaFinite (ν.map (fun y : ℝ => -y)) :=
    AvramDividend.Classical.gaussian_negative_jump_pushforward_sigmaFinite ν hν hlevy
  exact SigmaFinite.of_map ν measurable_neg.aemeasurable hpush
