-- Prove2me | solution 1 for F_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:34:17.94903+00:00
-- url     : https://prove2.me/submissions/3b57eeb0-0ea0-41de-89f0-938ba82d603e

import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Definitions.Def_PrimeNumberTheoremAnd_Sobolev
import Definitions.Def_PrimeNumberTheoremAnd_Fourier

set_option autoImplicit true
open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators
theorem _root_.solution {f : ℝ → ℂ} {c : ℂ} {u : ℝ} :
    𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  exact congr_fun (VectorFourier.fourierIntegral_const_smul 𝐞 _ _ f c) u
