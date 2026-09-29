-- Prove2me | solution 1 for CelestialHolography.nullVector_null_future
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T19:37:31.272308+00:00
-- url     : https://prove2.me/submissions/4f6983ca-4bb7-4879-bba8-727c0208eba3

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

set_option autoImplicit false

open CelestialHolography in
theorem solution (z : ℂ) :
    minkowskiNormSq (nullVector z) = 0 ∧ 0 < nullVector z 0 := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · simp only [minkowskiNormSq, nullVector, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Complex.normSq_apply, div_pow, h2]
    ring
  · simp only [nullVector, Matrix.cons_val_zero]
    exact div_pos (by linarith [Complex.normSq_nonneg z]) hs
