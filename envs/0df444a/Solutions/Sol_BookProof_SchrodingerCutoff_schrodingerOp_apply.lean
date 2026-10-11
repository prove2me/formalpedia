-- Prove2me | solution 1 for BookProof.SchrodingerCutoff.schrodingerOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:10:30.921457+00:00
-- url     : https://prove2.me/submissions/a7313c83-215a-4667-b5e2-6e3391bdb0c3

-- Generated from ChapterSchrodingerCutoffEsa.lean — solution of BookProof.SchrodingerCutoff.schrodingerOp_apply
import Mathlib
import Definitions.Def_ChapterSchrodingerCutoffEsa
open BookProof.SchrodingerCutoff




open MeasureTheory Filter Complex

set_option maxHeartbeats 1000000 in

theorem solution (V : ℝ → ℝ) (f f' f'' : ℝ → ℂ)
    (hf1 : ∀ x, HasDerivAt f (f' x) x) (hf2 : ∀ x, HasDerivAt f' (f'' x) x) (x : ℝ) :
    schrodingerOp V f x = -f'' x + (V x : ℂ) * f x := by
  have hfd : deriv f = f' := funext fun y => (hf1 y).deriv
  simp only [schrodingerOp, hfd, (hf2 x).deriv]
