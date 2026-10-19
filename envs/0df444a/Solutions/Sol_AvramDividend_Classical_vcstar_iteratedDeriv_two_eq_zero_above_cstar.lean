-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_iteratedDeriv_two_eq_zero_above_cstar
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T07:50:08.445769+00:00
-- url     : https://prove2.me/submissions/b16f8bfa-0ed4-4bd0-8df2-fcb2829e88c8

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution (W : ℝ → ℝ) (x : ℝ)
    (hx : (cstar W).toReal < x) :
    iteratedDeriv 2 (vcstar W) x = 0 := by
  let a := (cstar W).toReal
  let C := -(a : ℝ) + divE (W a) (scaleDeriv W a)
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hbranch : Set.EqOn (vcstar W) (fun z : ℝ => C + z) (Ioi a) := by
    intro z hz
    have hz0 : ¬ z < 0 := not_lt.mpr (ha.trans hz.le)
    have hza : ¬ z ≤ a := not_le.mpr hz
    change barrierValue W a z = C + z
    simp only [barrierValue, if_neg hz0, if_neg hza]
    dsimp [C]
    ring
  have hderiv : iteratedDeriv 2 (vcstar W) x =
      iteratedDeriv 2 (fun z : ℝ => C + z) x := by
    exact (hbranch.iteratedDeriv_of_isOpen isOpen_Ioi 2) hx
  rw [iteratedDeriv_const_add (by norm_num : 0 < (2 : ℕ)) C] at hderiv
  change iteratedDeriv 2 (vcstar W) x =
    iteratedDeriv 2 (id : ℝ → ℝ) x at hderiv
  simpa [iteratedDeriv_id] using hderiv