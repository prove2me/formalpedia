-- Prove2me | solution 1 for ConservationLaws.momentum_conservation_of_third_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T20:57:29.371229+00:00
-- url     : https://prove2.me/submissions/63a4bd69-d01a-4e7e-9622-db16146b0f7c

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {d N : ℕ} (m : Fin N → ℝ) (hm : ∀ i, 0 < m i)
    (v a : Fin N → ℝ → EuclideanSpace ℝ (Fin d))
    (F : Fin N → Fin N → ℝ → EuclideanSpace ℝ (Fin d))
    (hthird : ∀ i j t, F i j t = -F j i t)
    (hv : ∀ i t, HasDerivAt (v i) (a i t) t)
    (hnewton : ∀ i t, m i • a i t = ∑ j, F i j t) :
    ∀ t s, ∑ i, m i • v i t = ∑ i, m i • v i s := by
  let P : ℝ → EuclideanSpace ℝ (Fin d) :=
    fun t => ∑ i, m i • v i t
  have hforce (t : ℝ) :
      (∑ i, ∑ j, F i j t) = 0 := by
    let B : EuclideanSpace ℝ (Fin d) := ∑ i, ∑ j, F i j t
    have hneg : B = -B := by
      calc
        B = ∑ i, ∑ j, -(F j i t) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hthird i j t
        _ = -(∑ i, ∑ j, F j i t) := by simp
        _ = -B := by
          congr 1
          exact Finset.sum_comm
    have htwice : (2 : ℝ) • B = 0 := by
      calc
        (2 : ℝ) • B = B + B := by
          rw [show (2 : ℝ) = 1 + 1 by norm_num, add_smul, one_smul]
        _ = 0 := by
          calc
            B + B = B + -B := congrArg (fun z => B + z) hneg
            _ = 0 := add_neg_cancel B
    have hz : B = 0 :=
      (smul_eq_zero.mp htwice).resolve_left (by norm_num : (2 : ℝ) ≠ 0)
    exact hz
  have hderiv (t : ℝ) : HasDerivAt P 0 t := by
    have hd : HasDerivAt P (∑ i, m i • a i t) t := by
      apply HasDerivAt.fun_sum
      intro i hi
      exact (hv i t).const_smul (m i)
    have hzero : (∑ i, m i • a i t) = 0 := by
      calc
        (∑ i, m i • a i t) = ∑ i, ∑ j, F i j t := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hnewton i t
        _ = 0 := hforce t
    simpa only [hzero] using hd
  have hdiff : Differentiable ℝ P :=
    fun t => (hderiv t).differentiableAt
  have hzero : ∀ t, deriv P t = 0 :=
    fun t => (hderiv t).deriv
  intro t s
  exact is_const_of_deriv_eq_zero hdiff hzero t s
