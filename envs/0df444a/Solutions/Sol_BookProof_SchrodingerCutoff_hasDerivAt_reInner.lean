-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.hasDerivAt_reInner
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T14:50:33.863204+00:00
-- url     : https://prove2.me/submissions/24b4351e-7279-4398-8b57-49bf76ec3c67

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.hasDerivAt_reInner
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in
theorem solution (u u' u'' : ℝ → ℂ) (x : ℝ)
    (h1 : HasDerivAt u (u' x) x) (h2 : HasDerivAt u' (u'' x) x) :
    HasDerivAt (fun y => ((starRingEnd ℂ) (u y) * u' y).re)
      (‖u' x‖ ^ 2 + ((starRingEnd ℂ) (u x) * u'' x).re) x := by

  have hc : HasDerivAt (fun y => (starRingEnd ℂ) (u y)) ((starRingEnd ℂ) (u' x)) x := h1.star
  have hp : HasDerivAt (fun y => (starRingEnd ℂ) (u y) * u' y)
      ((starRingEnd ℂ) (u' x) * u' x + (starRingEnd ℂ) (u x) * u'' x) x := hc.mul h2
  simpa [Function.comp_def, Complex.reCLM_apply, Complex.add_re, Complex.mul_re,
    Complex.sq_norm, Complex.normSq_apply] using
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hp)
