-- Prove2me | solution 1 for BianchiIX.hasDerivAt_wallAmplitude
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T05:41:04.226199+00:00
-- url     : https://prove2.me/submissions/2c99a884-1a1d-4ffc-bdfd-807bf31f00f0

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Algebra_Flux
import Theorems.Thm_BianchiIX_hasDerivAt_wall_product
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp

open BianchiIX
noncomputable section


theorem solution
    {p s a b c : ℝ → ℝ} {t : ℝ}
    (ha : HasDerivAt a (rateOne (p t) (s t) * a t) t)
    (hb : HasDerivAt b (rateTwo (p t) (s t) * b t) t)
    (hc : HasDerivAt c (rateThree (p t) (s t) * c t) t)
    (ha0 : 0 < a t) (hb0 : 0 < b t) (hc0 : 0 < c t) :
    HasDerivAt (fun x => wallAmplitude (a x) (b x) (c x))
      (-2 * shearSq (p t) (s t) * wallAmplitude (a t) (b t) (c t)) t := by
  have hne : a t * b t * c t ≠ 0 := ne_of_gt (mul_pos (mul_pos ha0 hb0) hc0)
  have h := (hasDerivAt_wall_product ha hb hc).rpow_const
    (p := (2 / 3 : ℝ)) (Or.inl hne)
  convert h using 1 <;> first | rfl | (
    unfold wallAmplitude
    rw [Real.rpow_sub_one hne]
    field_simp)
