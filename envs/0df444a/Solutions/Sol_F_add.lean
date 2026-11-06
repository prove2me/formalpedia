-- Prove2me | solution 1 for F_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:35:20.522778+00:00
-- url     : https://prove2.me/submissions/c120b2e5-9e4e-43e6-9ea3-7319098ee26f

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
import Definitions.Def_PrimeNumberTheoremAnd_Fourier
import Theorems.Thm_W21_hf


set_option autoImplicit true
open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators
theorem _root_.solution {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x := by
  exact congr_fun (fourierIntegral_add continuous_fourierChar continuous_inner hf hg) x
