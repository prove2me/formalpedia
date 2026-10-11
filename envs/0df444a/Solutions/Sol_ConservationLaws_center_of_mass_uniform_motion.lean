-- Prove2me | solution 1 for ConservationLaws.center_of_mass_uniform_motion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T21:01:55.044712+00:00
-- url     : https://prove2.me/submissions/16637634-7542-47d9-9474-9a3ff6e6ae8f

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.NormNum

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {d N : ℕ} (hN : 0 < N) (m : Fin N → ℝ) (hm : ∀ i, 0 < m i)
    (x v a : Fin N → ℝ → EuclideanSpace ℝ (Fin d))
    (F : Fin N → Fin N → ℝ → EuclideanSpace ℝ (Fin d))
    (hthird : ∀ i j t, F i j t = -F j i t)
    (hx : ∀ i t, HasDerivAt (x i) (v i t) t)
    (hv : ∀ i t, HasDerivAt (v i) (a i t) t)
    (hnewton : ∀ i t, m i • a i t = ∑ j, F i j t) :
    ∀ t, (∑ i, m i)⁻¹ • ∑ i, m i • x i t =
      (∑ i, m i)⁻¹ • ∑ i, m i • x i 0 +
        t • ((∑ i, m i)⁻¹ • ∑ i, m i • v i 0) := by
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
  have hP (t : ℝ) : P t = P 0 :=
    is_const_of_deriv_eq_zero hdiff hzero t 0
  let R : ℝ → EuclideanSpace ℝ (Fin d) :=
    fun t => (∑ i, m i)⁻¹ • ∑ i, m i • x i t
  let V : EuclideanSpace ℝ (Fin d) :=
    (∑ i, m i)⁻¹ • P 0
  have hR (t : ℝ) : HasDerivAt R V t := by
    have hs : HasDerivAt (fun q => ∑ i, m i • x i q)
        (∑ i, m i • v i t) t := by
      apply HasDerivAt.fun_sum
      intro i hi
      exact (hx i t).const_smul (m i)
    have hr := hs.const_smul ((∑ i, m i)⁻¹)
    change HasDerivAt R ((∑ i, m i)⁻¹ • P t) t at hr
    rw [hP t] at hr
    exact hr
  have hline (t : ℝ) : HasDerivAt (fun q => R q - q • V) 0 t := by
    have hid : HasDerivAt (fun q : ℝ => q • V) V t := by
      simpa only [id, one_smul] using (hasDerivAt_id t).smul_const V
    have hh : HasDerivAt (fun q => R q - q • V) (V - V) t :=
      (hR t).sub hid
    simpa only [sub_self] using hh
  have hlinediff : Differentiable ℝ (fun q => R q - q • V) :=
    fun q => (hline q).differentiableAt
  have hlinezero : ∀ q, deriv (fun r => R r - r • V) q = 0 :=
    fun q => (hline q).deriv
  intro t
  have he := is_const_of_deriv_eq_zero hlinediff hlinezero t 0
  change R t - t • V = R 0 - (0 : ℝ) • V at he
  simp only [zero_smul, sub_zero] at he
  have hr : R t = R 0 + t • V := (sub_eq_iff_eq_add).mp he
  exact hr
