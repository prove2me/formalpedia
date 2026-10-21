-- Prove2me | solution 1 for AvramDividend.Classical.barrierValue_contDiffOn_Ioo_of_scaleFunction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:03:44.198982+00:00
-- url     : https://prove2.me/submissions/284b3e1f-374c-45a5-bf3a-21f704ae6d24

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped ENNReal
open AvramDividend.Classical

/-
Below the barrier level the barrier value is the scale function divided by
its derivative at the barrier level, so the regularity of the barrier value
below the barrier is the regularity of the scale function, the division being
by a positive constant.
-/

open AvramDividend.Classical

theorem solution
    (W : ℝ → ℝ) (a : ℝ) (n : ℕ) (ha : 0 < a)
    (hder : 0 < deriv W a)
    (hWdiff : ContDiffOn ℝ n W (Ioo 0 a)) :
    ContDiffOn ℝ n (barrierValue W a) (Ioo 0 a) := by
  -- The normalising factor is a positive constant, because the barrier level
  -- is positive and the derivative there is positive.
  -- On `(0, a)` the barrier value is the normalised scale function.
  have hbv : ∀ x ∈ Ioo 0 a,
      barrierValue W a x = divE (W x) (scaleDeriv W a) := by
    intro x hx
    have hx0 : ¬ x < 0 := not_lt.mpr hx.1.le
    have hxa : x ≤ a := le_of_lt hx.2
    simp only [barrierValue, if_neg hx0, if_pos hxa]
  -- The normalised scale function is as regular as the scale function, the
  -- denominator being a positive constant.
  have hscaled : ContDiffOn ℝ n
      (fun z : ℝ => divE (W z) (scaleDeriv W a)) (Ioo 0 a) := by
    let k : ℝ := (deriv W a)⁻¹
    have ha0 : a ≠ 0 := ne_of_gt ha
    have hfun :
        (fun z : ℝ => divE (W z) (scaleDeriv W a)) =
          (fun z : ℝ => k * W z) := by
      funext z
      simp [divE, scaleDeriv, ha0, k, div_eq_mul_inv, mul_comm]
    rw [hfun]
    simpa only [smul_eq_mul] using (ContDiffOn.const_smul k hWdiff)
  exact hscaled.congr hbv
