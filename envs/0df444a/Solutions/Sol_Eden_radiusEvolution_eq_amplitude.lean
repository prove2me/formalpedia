-- Prove2me | solution 1 for Eden.radiusEvolution_eq_amplitude
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:29:07.559635+00:00
-- url     : https://prove2.me/submissions/8c20884f-012f-4bb8-8fa5-555c709b9764

import Definitions.Def_Eden_PhysicalRadius
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Eden_AngularLifts
import Theorems.Thm_Eden_mul_amplitudeSq
import Theorems.Thm_Eden_planarAmplitude_pos
import Theorems.Thm_Eden_planarAmplitude_sq
import Theorems.Thm_Eden_radiusEvolution_nonneg
import Theorems.Thm_Eden_radiusEvolution_sq


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) :
    radiusEvolution t r = r * planarAmplitude t (r ^ 2) := by
  have h₁ := radiusEvolution_sq ht r
  have h₂ := planarAmplitude_sq ht (sq_nonneg r)
  have h₃ := mul_amplitudeSq ht (r ^ 2)
  have hn := radiusEvolution_nonneg t r
  have hg := planarAmplitude_pos ht (sq_nonneg r)
  have hp := mul_nonneg hr hg.le
  nlinarith [sq_nonneg (radiusEvolution t r + r * planarAmplitude t (r ^ 2)),
    congrArg (fun a : ℝ => r ^ 2 * a) h₂]
end Eden
