-- Prove2me | solution 1 for FockSPR.monomial_integral_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:09:14.689851+00:00
-- url     : https://prove2.me/submissions/5c6d4294-da33-43b3-851d-0445333320ca

module
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_LaplaceFactorial
public import Theorems.Thm_FockSPR_phiFunc_quad_bound
public import Theorems.Thm_FockSPR_exp_phi_le_factorial
section
@[expose] public section
open Real MeasureTheory Set
noncomputable section
namespace FockSPR
private lemma distToInterval_nonneg (x : ℝ) (j : ℕ) : 0 ≤ distToInterval x j :=
  le_max_right _ _
private lemma distToInterval_le_abs_sub (x r : ℝ) (j : ℕ)
    (hrj : (j : ℝ) ≤ r) (hrj1 : r ≤ (j : ℝ) + 1) :
    distToInterval x j ≤ |r - x| := by
  unfold distToInterval
  exact max_le
    (max_le (by
      linarith only [
        hrj, le_abs_self (r - x)
      ]) (by linarith only [hrj1, neg_le_abs (r - x)]))
    (abs_nonneg _)
private lemma distToInterval_sq_le_sq (x r : ℝ) (j : ℕ)
    (hrj : (j : ℝ) ≤ r) (hrj1 : r ≤ (j : ℝ) + 1) :
    distToInterval x j ^ 2 ≤ (r - x) ^ 2 := by
  have h1 := distToInterval_le_abs_sub x r j hrj hrj1
  have h2 := distToInterval_nonneg x j
  calc distToInterval x j ^ 2
      ≤ |r - x| ^ 2 := by nlinarith only [h1, h2, sq_nonneg (|r - x| - distToInterval x j)]
    _ = (r - x) ^ 2 := sq_abs _
private lemma pointwise_bound {n : ℕ} (hn : 1 ≤ n) {r : ℝ}
    {j : ℕ} (hrj : (j : ℝ) ≤ r) (hrj1 : r ≤ (j : ℝ) + 1) :
    r ^ (2 * n + 1) * Real.exp (-r ^ 2) ≤
    Real.exp (1 / 4) * (Nat.factorial n : ℝ) / 2 *
      Real.exp (-(distToInterval (rStar n) j) ^ 2) := by
  by_cases hr : r = 0
  · subst hr
    simp only [zero_pow (by omega : 2 * n + 1 ≠ 0), zero_mul]
    positivity
  · have hr_pos : 0 < r :=
      lt_of_le_of_ne (le_trans (Nat.cast_nonneg j) hrj) (Ne.symm hr)
    have h_eq : r ^ (2 * n + 1) * Real.exp (-r ^ 2) = Real.exp (phiFunc n r) := by
      unfold phiFunc
      have : r ^ (2 * n + 1) = Real.exp ((2 * ↑n + 1 : ℝ) * Real.log r) := by
        rw [← Real.exp_log hr_pos, ← Real.exp_nsmul]
        simp only [nsmul_eq_mul, Real.log_exp, Nat.cast_add, Nat.cast_mul,
          Nat.cast_ofNat, Nat.cast_one]
      rw [this, ← Real.exp_add]; ring_nf
    rw [h_eq]
    calc Real.exp (phiFunc n r)
        ≤ Real.exp (phiFunc n (rStar n) - distToInterval (rStar n) j ^ 2) :=
          Real.exp_le_exp.mpr
            (by linarith only [phiFunc_quad_bound hn hr_pos,
                distToInterval_sq_le_sq (rStar n) r j hrj hrj1])
      _ = Real.exp (phiFunc n (rStar n)) *
          Real.exp (-(distToInterval (rStar n) j ^ 2)) := by rw [sub_eq_add_neg, Real.exp_add]
      _ ≤ (Real.exp (1 / 4) * ↑n.factorial / 2) *
          Real.exp (-(distToInterval (rStar n) j ^ 2)) :=
          mul_le_mul_of_nonneg_right (exp_phi_le_factorial hn)
            (le_of_lt (Real.exp_pos _))
      _ = Real.exp (1 / 4) * ↑n.factorial / 2 *
          Real.exp (-(distToInterval (rStar n) j) ^ 2) := by ring
end FockSPR
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Real MeasureTheory Set
noncomputable section
open FockSPR
namespace FockSPR
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) (j : ℕ) :
    ∫ r in (j : ℝ)..(j + 1 : ℝ), r ^ (2 * n + 1) * Real.exp (-r ^ 2) ≤
      Real.exp (1 / 4) * (Nat.factorial n : ℝ) / 2 *
        Real.exp (-(distToInterval (rStar n) j) ^ 2) := by
  set C := Real.exp (1 / 4) * (Nat.factorial n : ℝ) / 2 *
    Real.exp (-(distToInterval (rStar n) j) ^ 2)
  have h_const : ∫ r in (j : ℝ)..(↑j + 1), C = C := integral_const_on_unit_interval
  rw [← h_const]
  apply intervalIntegral.integral_mono_on (by linarith only [] : (j : ℝ) ≤ ↑j + 1)
  · apply ContinuousOn.intervalIntegrable
    exact (continuousOn_pow _).mul
      ((Real.continuous_exp.comp
        (continuous_neg.comp (continuous_pow 2))).continuousOn)
  · exact ContinuousOn.intervalIntegrable continuousOn_const
  · intro r hr
    exact pointwise_bound hn hr.1 hr.2
end FockSPR
