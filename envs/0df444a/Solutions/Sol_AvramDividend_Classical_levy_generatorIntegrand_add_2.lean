-- Prove2me | solution 2 for AvramDividend.Classical.levy_generatorIntegrand_add
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:39:15.149319+00:00
-- url     : https://prove2.me/submissions/8fc399f3-4c88-4fb9-b15a-7bb10ab8b423

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
open AvramDividend.Classical.SpectrallyNegativeLevy

theorem solution
    (f g : ℝ → ℝ) (a b x y : ℝ)
    (hf : HasDerivAt f a x) (hg : HasDerivAt g b x) :
    generatorIntegrand (fun z => f z + g z) x y =
      generatorIntegrand f x y + generatorIntegrand g x y := by
  unfold generatorIntegrand
  have h : deriv (fun z => f z + g z) x = deriv f x + deriv g x :=
    (hf.differentiableAt.hasDerivAt.add hg.differentiableAt.hasDerivAt).deriv
  rw [h]
  ring
