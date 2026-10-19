-- Prove2me | solution 1 for AvramDividend.Classical.scaledW_second_deriv_zero_at_positive_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:38:29.796613+00:00
-- url     : https://prove2.me/submissions/abcec164-809d-4beb-a498-5bd85a5e1258

import Mathlib.Analysis.Calculus.Deriv.Mul
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_deriv_deriv_eq_zero_at_positive_cstar_of_deriv_continuous

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (W : ℝ → ℝ)
    (hcont : ContinuousOn (deriv W) (Ioi 0))
    (hpos : 0 < (cstar W).toReal) :
    deriv (deriv
      (fun z : ℝ => divE (W z) (scaleDeriv W (cstar W).toReal)))
      (cstar W).toReal = 0 := by
  let a : ℝ := (cstar W).toReal
  let D : EReal := scaleDeriv W a
  let c : ℝ := D.toReal
  let u : ℝ → ℝ := fun z => divE (W z) D
  have ha : 0 < a := hpos
  have hdtop : D ≠ ⊤ := by
    simp [D, scaleDeriv, ne_of_gt ha]
  have hfunc : u = fun z : ℝ => W z / c := by
    funext z
    simp only [u, divE, if_neg hdtop, c]
  have hderivfunc : deriv u = fun z : ℝ => deriv W z / c := by
    funext z
    rw [hfunc]
    exact deriv_div_const c
  have hzero : deriv (deriv W) a = 0 :=
    deriv_deriv_eq_zero_at_positive_cstar_of_deriv_continuous W hcont hpos
  change deriv (deriv u) a = 0
  calc
    deriv (deriv u) a =
      deriv (fun z : ℝ => deriv W z / c) a := by rw [hderivfunc]
    _ = deriv (deriv W) a / c := deriv_div_const c
    _ = 0 := by rw [hzero]; simp
