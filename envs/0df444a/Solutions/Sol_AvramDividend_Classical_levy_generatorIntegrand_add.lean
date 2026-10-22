-- Prove2me | solution 1 for AvramDividend.Classical.levy_generatorIntegrand_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T06:45:55.427282+00:00
-- url     : https://prove2.me/submissions/0bac6233-e1d2-4b51-b016-5f712e46a32e

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
open AvramDividend.Classical.SpectrallyNegativeLevy

theorem solution
    (f g : ℝ → ℝ) (a b x y : ℝ)
    (hf : HasDerivAt f a x) (hg : HasDerivAt g b x) :
    generatorIntegrand (fun z => f z + g z) x y =
      generatorIntegrand f x y + generatorIntegrand g x y := by
  have hderiv :
      deriv (fun z => f z + g z) x = deriv f x + deriv g x := by
    change deriv (f + g) x = deriv f x + deriv g x
    calc
      deriv (f + g) x = a + b := (hf.add hg).deriv
      _ = deriv f x + deriv g x := by
        rw [hf.deriv, hg.deriv]
  simp only [generatorIntegrand, hderiv]
  ring
