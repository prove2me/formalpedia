-- Prove2me | solution 1 for BLTCounting.AccuracySpace.corollary_3_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:01:54.987983+00:00
-- url     : https://prove2.me/submissions/27f269a5-dae5-41b0-9da0-1f7155bb1f22
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BLTCounting_AccuracySpace_FourierKernel
import Theorems.Thm_BLTCounting_AccuracySpace_claim_3_8
import Theorems.Thm_BLTCounting_AccuracySpace_lemma_3_7

open BLTCounting.AccuracySpace

theorem solution (h θ : ℝ) (hh : 0 < h) (hθ : θ ∈ Set.Icc (-Real.pi) Real.pi) :
    (sampledSymbol h θ).im = 0 ∧
      (1 / h) * (c0Hat (θ / h)).re ≤ (sampledSymbol h θ).re := by
  have h38 := (claim_3_8 h θ hh hθ).2
  have h37 := lemma_3_7.1
  have him : HasSum (fun p : ℤ => (((1 / h : ℝ) : ℂ) * c0Hat ((θ + 2 * Real.pi * p) / h)).im)
      (sampledSymbol h θ).im := Complex.imCLM.hasSum h38
  have him_zero : (fun p : ℤ => (((1 / h : ℝ) : ℂ) * c0Hat ((θ + 2 * Real.pi * p) / h)).im) =
      fun _ => 0 := by
    ext p
    have hp := (h37 ((θ + 2 * Real.pi * p) / h)).1
    simp [Complex.mul_im, hp]
  rw [him_zero] at him
  have hre : HasSum (fun p : ℤ => (((1 / h : ℝ) : ℂ) * c0Hat ((θ + 2 * Real.pi * p) / h)).re)
      (sampledSymbol h θ).re := Complex.reCLM.hasSum h38
  have hre_simp : (fun p : ℤ => (((1 / h : ℝ) : ℂ) * c0Hat ((θ + 2 * Real.pi * p) / h)).re) =
      fun p : ℤ => (1 / h) * (c0Hat ((θ + 2 * Real.pi * p) / h)).re := by
    ext p
    have hp := (h37 ((θ + 2 * Real.pi * p) / h)).1
    simp [Complex.mul_re, hp]
  rw [hre_simp] at hre
  refine ⟨him.unique hasSum_zero, ?_⟩
  have h0 := le_hasSum hre (0 : ℤ) fun p _ =>
    mul_nonneg (by positivity) (h37 ((θ + 2 * Real.pi * p) / h)).2.1
  simpa using h0
