-- Prove2me | solution 1 for D1Bound5.full_ring_finitePDividedMatrix_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-23T23:50:34.510986+00:00
-- url     : https://prove2.me/submissions/2f2bc09b-3f14-4f53-9fd1-4762b8aece59

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.GCD
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FinitePMatrix_Definitions
import Theorems.Thm_D1Bound5_finitePDividedMatrix_det
import Theorems.Thm_D1Bound5_full_ring_finitePDetFactor_ne_zero

section
open scoped NumberField
open Module

namespace D1Bound5















theorem _root_.solution
    {K : Type*} [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (hK : finrank ℚ K = 2) (phi : K →+* ℂ) (a b s c : 𝓞 K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hs : s ≠ 0)
    (hab : a ≠ b) (has : a ≠ s) (hbs : b ≠ s)
    (hAB : ‖phi (a : K)‖ ≤ ‖phi (b : K)‖)
    (hBS : ‖phi (b : K)‖ ≤ ‖phi (s : K)‖)
    (hC : 200*‖phi (s : K)‖ ≤ ‖phi (c : K)‖) :
    (finitePDividedMatrix (phi (a : K)) (phi (b : K)) (phi (s : K)) (phi (c : K))).det ≠ 0 := by
  let f : 𝓞 K →+* ℂ := phi.comp (algebraMap (𝓞 K) K)
  have hf : Function.Injective f := by
    intro x y hxy
    apply NumberField.RingOfIntegers.ext
    exact phi.injective hxy
  have hn (x : 𝓞 K) (hx : x ≠ 0) : f x ≠ 0 := by
    intro h
    exact hx (hf (by simpa only [map_zero] using h))
  have hfac := full_ring_finitePDetFactor_ne_zero hK phi a b s c hs hab hAB hBS hC
  change (finitePDividedMatrix (f a) (f b) (f s) (f c)).det ≠ 0
  rw [finitePDividedMatrix_det]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (by norm_num : (-78750 : ℂ) ≠ 0) (hn a ha)) (hn b hb))
      (hn s hs)) (pow_ne_zero _ (sub_ne_zero.mpr (fun h => hab (hf h)))))
        (sub_ne_zero.mpr (fun h => has (hf h))))
          (sub_ne_zero.mpr (fun h => hbs (hf h)))) hfac







end D1Bound5
end
