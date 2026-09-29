-- Prove2me | solution 1 for DixmierMalliavin.exists_contDiff_tendsto_integral_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8ab85fb1-a232-5823-b8a6-d6500448bded

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Order.LeftRight
import Mathlib.Topology.Order.MonotoneConvergence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul

set_option autoImplicit false

noncomputable section

open Finset Filter Topology

namespace OneVariableFactorization

private structure KernelGood (lam : ℕ → ℝ) : Prop where
  four_le : 4 ≤ lam 0
  double : ∀ n, 2 * lam n ≤ lam (n + 1)
  prodBound : ∀ n, (4 : ℝ) ^ n * ∏ j ∈ range n, (lam j) ^ 2 ≤ lam n

private def uOf (lam : ℕ → ℝ) (n : ℕ) : ℝ := 1 / (lam n) ^ 2

private def _root_.OneVariableFactorization.shift (lam : ℕ → ℝ) (n : ℕ) : ℝ := lam (n + 1)

p2m_export "OneVariableFactorization" "shift"
namespace KernelGood

variable {lam : ℕ → ℝ}

private theorem four_le_all (h : KernelGood lam) : ∀ n, 4 ≤ lam n := by
  intro n
  induction n with
  | zero => exact h.four_le
  | succ n ih => have := h.double n; linarith

private theorem one_le (h : KernelGood lam) (n : ℕ) : 1 ≤ lam n := by linarith [h.four_le_all n]

private theorem pos (h : KernelGood lam) (n : ℕ) : 0 < lam n := by linarith [h.four_le_all n]

private theorem ne_zero (h : KernelGood lam) (n : ℕ) : lam n ≠ 0 := (h.pos n).ne'

private theorem le_succ (h : KernelGood lam) (n : ℕ) : lam n ≤ lam (n + 1) := by
  have := h.double n; have := h.pos n; linarith

private theorem mono (h : KernelGood lam) : Monotone lam := monotone_nat_of_le_succ h.le_succ

private theorem mul_two_pow_le (h : KernelGood lam) (i : ℕ) : ∀ k : ℕ, lam i * (2 : ℝ) ^ k ≤ lam (i + k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 := h.double (i + k)
    have h3 : lam i * (2 : ℝ) ^ (k + 1) = (lam i * 2 ^ k) * 2 := by ring
    rw [h3, show i + (k + 1) = i + k + 1 by omega]
    linarith

private theorem shift (h : KernelGood lam) : KernelGood (OneVariableFactorization.shift lam) where
  four_le := by
    have h0 := h.four_le
    have h1 := h.double 0
    simp only [OneVariableFactorization.shift]
    linarith
  double n := h.double (n + 1)
  prodBound n := by
    have hb := h.prodBound (n + 1)
    rw [prod_range_succ'] at hb
    have h0 : (1 : ℝ) ≤ (lam 0) ^ 2 := by nlinarith [h.one_le 0]
    have hp : 0 ≤ ∏ j ∈ range n, (lam (j + 1)) ^ 2 := prod_nonneg (fun j _ => sq_nonneg _)
    have h4 : (0 : ℝ) < 4 ^ n := pow_pos (by norm_num) n
    have h4' : (4 : ℝ) ^ n ≤ 4 ^ (n + 1) := by rw [pow_succ]; nlinarith
    simp only [OneVariableFactorization.shift]
    calc (4 : ℝ) ^ n * ∏ j ∈ range n, (lam (j + 1)) ^ 2
        ≤ 4 ^ (n + 1) * ((∏ j ∈ range n, (lam (j + 1)) ^ 2) * (lam 0) ^ 2) := by
          have : (4 : ℝ) ^ n * ∏ j ∈ range n, (lam (j + 1)) ^ 2 ≤ 4 ^ (n + 1) * ∏ j ∈ range n, (lam (j + 1)) ^ 2 :=
            mul_le_mul_of_nonneg_right h4' hp
          have h5 : 0 ≤ (4 : ℝ) ^ (n + 1) := by positivity
          nlinarith [mul_nonneg h5 hp]
      _ ≤ lam (n + 1) := hb

private theorem uOf_pos (h : KernelGood lam) (n : ℕ) : 0 < uOf lam n := by
  unfold uOf; have := h.pos n; positivity

private theorem uOf_nonneg (h : KernelGood lam) (n : ℕ) : 0 ≤ uOf lam n := (h.uOf_pos n).le

private theorem uOf_succ_le (h : KernelGood lam) (n : ℕ) : uOf lam (n + 1) ≤ uOf lam n / 4 := by
  unfold uOf
  have hn := h.pos n
  have hd := h.double n
  have hn1 : 0 < lam (n + 1) := h.pos (n + 1)
  rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hn hn, hd]

private theorem uOf_zero_le (h : KernelGood lam) : uOf lam 0 ≤ 1 / 16 := by
  unfold uOf
  have h0 := h.four_le
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

private theorem uOf_le_zero (h : KernelGood lam) (n : ℕ) : uOf lam n ≤ uOf lam 0 := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have h1 := h.uOf_succ_le n
    have h2 := h.uOf_nonneg n
    linarith

private theorem uOf_shift (n : ℕ) : uOf (OneVariableFactorization.shift lam) n = uOf lam (n + 1) := rfl

end KernelGood

private def ratio (lam : ℕ → ℝ) (i j : ℕ) : ℝ := (lam i) ^ 2 / (lam j) ^ 2

private theorem ratio_nonneg (lam : ℕ → ℝ) (i j : ℕ) : 0 ≤ ratio lam i j := by unfold ratio; positivity

private theorem ratio_shift (lam : ℕ → ℝ) (i j : ℕ) : ratio (shift lam) i j = ratio lam (i + 1) (j + 1) := rfl

private theorem four_le_ratio {lam : ℕ → ℝ} (h : KernelGood lam) {i j : ℕ} (hji : j < i) : 4 ≤ ratio lam i j := by
  unfold ratio
  have hj := h.pos j
  have hi : lam j * 2 ≤ lam i := by
    have := h.mul_two_pow_le j 1
    simp only [pow_one] at this
    have hmono := h.mono (show j + 1 ≤ i by omega)
    linarith
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_pos hj hj]

private theorem ratio_le_quarter_pow {lam : ℕ → ℝ} (h : KernelGood lam) (i k : ℕ) :
    ratio lam i (i + 1 + k) ≤ (1 / 4 : ℝ) ^ (k + 1) := by
  unfold ratio
  have hi := h.pos i
  have hmul := h.mul_two_pow_le i (k + 1)
  rw [show i + (k + 1) = i + 1 + k by omega] at hmul
  have hj : 0 < lam (i + 1 + k) := h.pos (i + 1 + k)
  have h2k : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  rw [div_le_iff₀ (by positivity)]

  have hsq : (lam i * 2 ^ (k + 1)) ^ 2 ≤ (lam (i + 1 + k)) ^ 2 := by
    have h0 : 0 ≤ lam i * 2 ^ (k + 1) := by positivity
    nlinarith
  have hq : ((1 : ℝ) / 4) ^ (k + 1) * (2 ^ (k + 1)) ^ 2 = 1 := by
    rw [← pow_mul, show (k + 1) * 2 = 2 * (k + 1) by ring, pow_mul]
    rw [← mul_pow]; norm_num
  calc (lam i) ^ 2 = (1 / 4 : ℝ) ^ (k + 1) * ((lam i * 2 ^ (k + 1)) ^ 2) := by
        rw [mul_pow, ← mul_assoc, mul_comm ((1 / 4 : ℝ) ^ (k + 1)), mul_assoc, hq, mul_one]
    _ ≤ (1 / 4 : ℝ) ^ (k + 1) * (lam (i + 1 + k)) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hsq; positivity

private theorem ratio_le_quarter {lam : ℕ → ℝ} (h : KernelGood lam) (i k : ℕ) : ratio lam i (i + 1 + k) ≤ 1 / 4 := by
  have h1 := ratio_le_quarter_pow h i k
  have h2 : ((1 : ℝ) / 4) ^ (k + 1) ≤ 1 / 4 := by
    rw [pow_succ]
    have h3 : ((1 : ℝ) / 4) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have h4 : (0 : ℝ) ≤ (1 / 4) ^ k := by positivity
    nlinarith
  exact h1.trans h2

private def tf (lam : ℕ → ℝ) (i k : ℕ) : ℝ := (1 - ratio lam i (i + 1 + k))⁻¹

private theorem one_le_tf {lam : ℕ → ℝ} (h : KernelGood lam) (i k : ℕ) : 1 ≤ tf lam i k := by
  unfold tf
  have h1 := (ratio_le_quarter h) i k
  have h0 := ratio_nonneg lam i (i + 1 + k)
  have hpos : 0 < 1 - ratio lam i (i + 1 + k) := by linarith
  rw [inv_eq_one_div, le_div_iff₀ hpos]
  linarith

private theorem tf_le_exp {lam : ℕ → ℝ} (h : KernelGood lam) (i k : ℕ) :
    tf lam i k ≤ Real.exp (2 * ratio lam i (i + 1 + k)) := by
  unfold tf
  set x := ratio lam i (i + 1 + k) with hx
  have h1 : x ≤ 1 / 4 := (ratio_le_quarter h) i k
  have h0 : 0 ≤ x := ratio_nonneg lam i (i + 1 + k)
  have hpos : 0 < 1 - x := by linarith
  have hA : (1 - x)⁻¹ ≤ 1 + 2 * x := by
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith
  have hB : 1 + 2 * x ≤ Real.exp (2 * x) := by
    have := Real.add_one_le_exp (2 * x); linarith
  exact hA.trans hB

private theorem tf_nonneg {lam : ℕ → ℝ} (h : KernelGood lam) (i k : ℕ) : 0 ≤ tf lam i k :=
  zero_le_one.trans ((one_le_tf h) i k)

private theorem tf_shift (lam : ℕ → ℝ) (i k : ℕ) : tf (shift lam) i k = tf lam (i + 1) k := by
  unfold tf
  rw [ratio_shift, show i + 1 + k + 1 = i + 1 + 1 + k by omega]

private def tailP (lam : ℕ → ℝ) (i M : ℕ) : ℝ := ∏ k ∈ range M, tf lam i k

private theorem tailP_zero (lam : ℕ → ℝ) (i : ℕ) : tailP lam i 0 = 1 := by simp [tailP]

private theorem tailP_succ (lam : ℕ → ℝ) (i M : ℕ) : tailP lam i (M + 1) = tailP lam i M * tf lam i M := by
  simp [tailP, prod_range_succ]

private theorem one_le_tailP {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) : ∀ M, 1 ≤ tailP lam i M := by
  intro M
  induction M with
  | zero => simp [tailP_zero]
  | succ M ih =>
    rw [tailP_succ]
    have := (one_le_tf h) i M
    nlinarith

private theorem tailP_nonneg {lam : ℕ → ℝ} (h : KernelGood lam) (i M : ℕ) : 0 ≤ tailP lam i M :=
  zero_le_one.trans ((one_le_tailP h) i M)

private theorem sum_ratio_le {lam : ℕ → ℝ} (h : KernelGood lam) (i M : ℕ) :
    ∑ k ∈ range M, ratio lam i (i + 1 + k) ≤ 1 / 3 := by
  have h1 : ∑ k ∈ range M, ratio lam i (i + 1 + k) ≤ ∑ k ∈ range M, (1 / 4 : ℝ) ^ (k + 1) :=
    sum_le_sum (fun k _ => (ratio_le_quarter_pow h) i k)
  have h2 : ∑ k ∈ range M, (1 / 4 : ℝ) ^ (k + 1) = (1 / 4) * ∑ k ∈ range M, (1 / 4 : ℝ) ^ k := by
    rw [mul_sum]; apply sum_congr rfl; intro k _; ring
  have h3 : ∑ k ∈ range M, (1 / 4 : ℝ) ^ k ≤ 4 / 3 := by
    rw [geom_sum_eq (by norm_num : (1 / 4 : ℝ) ≠ 1) M]
    have hp : (0 : ℝ) ≤ (1 / 4) ^ M := by positivity
    rw [div_le_iff_of_neg (by norm_num : (1 / 4 : ℝ) - 1 < 0)]
    linarith
  linarith

private theorem tailP_le_exp {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) :
    ∀ M, tailP lam i M ≤ Real.exp (2 * ∑ k ∈ range M, ratio lam i (i + 1 + k)) := by
  intro M
  induction M with
  | zero => simp [tailP_zero]
  | succ M ih =>
    rw [tailP_succ, sum_range_succ, mul_add, Real.exp_add]
    exact mul_le_mul ih ((tf_le_exp h) i M) ((tf_nonneg h) i M) (Real.exp_pos _).le

private def CB : ℝ := 3

private theorem exp_two_thirds_le : Real.exp (2 / 3) ≤ CB := by
  unfold CB
  have h1 := Real.add_one_le_exp (-(2 / 3 : ℝ))
  have h2 : Real.exp (2 / 3) * Real.exp (-(2 / 3 : ℝ)) = 1 := by
    rw [← Real.exp_add]; norm_num
  have h3 : 0 < Real.exp (-(2 / 3 : ℝ)) := Real.exp_pos _
  nlinarith [Real.exp_pos (2 / 3 : ℝ)]

private theorem tailP_le_CB {lam : ℕ → ℝ} (h : KernelGood lam) (i M : ℕ) : tailP lam i M ≤ CB := by
  refine ((tailP_le_exp h) i M).trans ?_
  refine le_trans ?_ exp_two_thirds_le
  apply Real.exp_le_exp.2
  have := (sum_ratio_le h) i M
  linarith

private theorem tailP_mono {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) : Monotone (tailP lam i) := by
  apply monotone_nat_of_le_succ
  intro M
  rw [tailP_succ]
  have h1 := (one_le_tf h) i M
  have h2 := (tailP_nonneg h) i M
  nlinarith

private theorem tailP_shift (lam : ℕ → ℝ) (i M : ℕ) : tailP (shift lam) i M = tailP lam (i + 1) M := by
  unfold tailP
  apply prod_congr rfl
  intro k _
  exact tf_shift lam i k

private def tail (lam : ℕ → ℝ) (i : ℕ) : ℝ := ⨆ M : ℕ, tailP lam i M

private theorem tailP_bddAbove {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) : BddAbove (Set.range (tailP lam i)) :=
  ⟨CB, by rintro _ ⟨M, rfl⟩; exact (tailP_le_CB h) i M⟩

private theorem tailP_le_tail {lam : ℕ → ℝ} (h : KernelGood lam) (i M : ℕ) : tailP lam i M ≤ tail lam i :=
  le_ciSup ((tailP_bddAbove h) i) M

private theorem one_le_tail {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) : 1 ≤ tail lam i := by
  have := (tailP_le_tail h) i 0
  rw [tailP_zero] at this
  exact this

private theorem tail_le_CB {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) : tail lam i ≤ CB :=
  ciSup_le (fun M => (tailP_le_CB h) i M)

private theorem tail_nonneg {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) : 0 ≤ tail lam i :=
  zero_le_one.trans ((one_le_tail h) i)

private theorem tendsto_tailP {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) :
    Tendsto (tailP lam i) atTop (𝓝 (tail lam i)) :=
  tendsto_atTop_ciSup ((tailP_mono h) i) ((tailP_bddAbove h) i)

private theorem tail_shift (lam : ℕ → ℝ) (i : ℕ) : tail (shift lam) i = tail lam (i + 1) := by
  unfold tail
  simp only [tailP_shift]

private def head (lam : ℕ → ℝ) (i : ℕ) : ℝ := ∏ j ∈ range i, (1 - ratio lam i j)⁻¹

private def coef (lam : ℕ → ℝ) (i : ℕ) : ℝ := head lam i * tail lam i

private def coefP (lam : ℕ → ℝ) (i M : ℕ) : ℝ := head lam i * tailP lam i M

private theorem head_zero (lam : ℕ → ℝ) : head lam 0 = 1 := by simp [head]

private theorem tendsto_coefP {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) :
    Tendsto (coefP lam i) atTop (𝓝 (coef lam i)) :=
  ((tendsto_tailP h) i).const_mul (head lam i)

private theorem abs_head_factor_le {lam : ℕ → ℝ} (h : KernelGood lam) {i j : ℕ} (hji : j < i) :
    |(1 - ratio lam i j)⁻¹| ≤ (4 / 3) * ((lam j) ^ 2 / (lam i) ^ 2) := by
  have hr := four_le_ratio h hji
  have hi := h.pos i
  have hj := h.pos j
  have hneg : 1 - ratio lam i j < 0 := by linarith
  rw [abs_inv, abs_of_neg hneg]

  have hrpos : 0 < ratio lam i j := by linarith
  have hkey : (lam j) ^ 2 / (lam i) ^ 2 = (ratio lam i j)⁻¹ := by
    unfold ratio; rw [inv_div]
  rw [hkey]
  have hm : 0 < -(1 - ratio lam i j) := by linarith
  rw [inv_le_iff_one_le_mul₀ hm]
  rw [show (4 / 3 : ℝ) * (ratio lam i j)⁻¹ * -(1 - ratio lam i j)
      = (4 / 3) * ((ratio lam i j)⁻¹ * ratio lam i j) - (4 / 3) * (ratio lam i j)⁻¹ by ring]
  rw [inv_mul_cancel₀ hrpos.ne']
  have hinv : (ratio lam i j)⁻¹ ≤ 1 / 4 := by
    rw [inv_eq_one_div]; exact (one_div_le_one_div_of_le (by norm_num) hr)
  linarith

private theorem abs_head_mul_pow_le {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) :
    |head lam i| * (lam i) ^ (2 * i) ≤ (1 / 3 : ℝ) ^ i * lam i := by
  have hi := h.pos i
  have h1 : |head lam i| ≤ ∏ j ∈ range i, ((4 / 3 : ℝ) * ((lam j) ^ 2 / (lam i) ^ 2)) := by
    unfold head
    rw [abs_prod]
    apply prod_le_prod (fun j _ => abs_nonneg _)
    intro j hj
    exact (abs_head_factor_le h) (mem_range.1 hj)
  have h2 : ∏ j ∈ range i, ((4 / 3 : ℝ) * ((lam j) ^ 2 / (lam i) ^ 2))
      = (4 / 3 : ℝ) ^ i * (∏ j ∈ range i, (lam j) ^ 2) / (lam i) ^ (2 * i) := by
    rw [prod_mul_distrib, prod_const, card_range, prod_div_distrib, prod_const, card_range, ← pow_mul]
    ring
  have hpow : (0 : ℝ) < (lam i) ^ (2 * i) := by positivity
  have h3 : |head lam i| * (lam i) ^ (2 * i) ≤ (4 / 3 : ℝ) ^ i * ∏ j ∈ range i, (lam j) ^ 2 := by
    have := mul_le_mul_of_nonneg_right (h1.trans h2.le) hpow.le
    rwa [div_mul_cancel₀ _ hpow.ne'] at this
  have h4 := h.prodBound i

  have h4pos : (0 : ℝ) < 4 ^ i := by positivity
  have hP : ∏ j ∈ range i, (lam j) ^ 2 ≤ lam i / 4 ^ i := by
    rw [le_div_iff₀ h4pos]; linarith
  have h5 : (4 / 3 : ℝ) ^ i * ∏ j ∈ range i, (lam j) ^ 2 ≤ (4 / 3 : ℝ) ^ i * (lam i / 4 ^ i) :=
    mul_le_mul_of_nonneg_left hP (by positivity)
  have h6 : (4 / 3 : ℝ) ^ i * (lam i / 4 ^ i) = (1 / 3 : ℝ) ^ i * lam i := by
    have h43 : (4 / 3 : ℝ) ^ i = 4 ^ i * (1 / 3) ^ i := by
      rw [← mul_pow]; norm_num
    have h4ne : (4 : ℝ) ^ i ≠ 0 := h4pos.ne'
    calc (4 / 3 : ℝ) ^ i * (lam i / 4 ^ i) = (1 / 3 : ℝ) ^ i * lam i * ((4 : ℝ) ^ i / 4 ^ i) := by
          rw [h43]; ring
      _ = (1 / 3 : ℝ) ^ i * lam i := by rw [div_self h4ne, mul_one]
  linarith [h3, h5, h6]

private theorem abs_head_mul_tail_bound {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ CB) :
    |head lam i * t| * (lam i) ^ (2 * i) ≤ CB * (1 / 3 : ℝ) ^ i * lam i := by
  rw [abs_mul, abs_of_nonneg ht0]
  have h1 := (abs_head_mul_pow_le h) i
  have hi := h.pos i
  have hpow : (0 : ℝ) ≤ (lam i) ^ (2 * i) := by positivity
  have h13 : (0 : ℝ) ≤ (1 / 3 : ℝ) ^ i * lam i := by positivity
  calc |head lam i| * t * (lam i) ^ (2 * i) = (|head lam i| * (lam i) ^ (2 * i)) * t := by ring
    _ ≤ ((1 / 3 : ℝ) ^ i * lam i) * CB := mul_le_mul h1 ht ht0 h13
    _ = CB * (1 / 3 : ℝ) ^ i * lam i := by ring

private theorem abs_coef_mul_pow_le {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) :
    |coef lam i| * (lam i) ^ (2 * i) ≤ CB * (1 / 3 : ℝ) ^ i * lam i :=
  (abs_head_mul_tail_bound h) i ((tail_nonneg h) i) ((tail_le_CB h) i)

private theorem abs_coefP_mul_pow_le {lam : ℕ → ℝ} (h : KernelGood lam) (i M : ℕ) :
    |coefP lam i M| * (lam i) ^ (2 * i) ≤ CB * (1 / 3 : ℝ) ^ i * lam i :=
  (abs_head_mul_tail_bound h) i ((tailP_nonneg h) i M) ((tailP_le_CB h) i M)

private theorem abs_mul_pow_le_of_core {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) {c : ℝ}
    (hc : |c| * (lam i) ^ (2 * i) ≤ CB * (1 / 3 : ℝ) ^ i * lam i) {m : ℕ} (hm : m + 1 ≤ 2 * i) :
    |c| * (lam i) ^ m ≤ CB * (1 / 3 : ℝ) ^ i := by
  have hi1 := h.one_le i
  have hipos : 0 < lam i := h.pos i
  obtain ⟨d, hd⟩ : ∃ d, 2 * i = m + 1 + d := ⟨2 * i - (m + 1), by omega⟩
  rw [hd, pow_add, pow_add, pow_one] at hc

  have hdpow : 1 ≤ (lam i) ^ d := one_le_pow₀ hi1
  have hc' : |c| * (lam i) ^ m * lam i ≤ CB * (1 / 3 : ℝ) ^ i * lam i := by
    have hx : |c| * (lam i) ^ m * lam i ≤ |c| * (lam i) ^ m * lam i * (lam i) ^ d := by
      have : 0 ≤ |c| * (lam i) ^ m * lam i := by positivity
      nlinarith
    calc |c| * (lam i) ^ m * lam i ≤ |c| * (lam i) ^ m * lam i * (lam i) ^ d := hx
      _ = |c| * ((lam i) ^ m * lam i * (lam i) ^ d) := by ring
      _ ≤ CB * (1 / 3 : ℝ) ^ i * lam i := hc
  exact le_of_mul_le_mul_right hc' hipos

private theorem one_le_lam_of_good {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) : 1 ≤ lam i := h.one_le i

private theorem abs_coef_mul_pow_le_geom {lam : ℕ → ℝ} (h : KernelGood lam) {i m : ℕ} (hm : m + 1 ≤ 2 * i) :
    |coef lam i| * (lam i) ^ m ≤ CB * (1 / 3 : ℝ) ^ i :=
  (abs_mul_pow_le_of_core h) i ((abs_coef_mul_pow_le h) i) hm

private theorem abs_coefP_mul_pow_le_geom {lam : ℕ → ℝ} (h : KernelGood lam) {i m : ℕ} (M : ℕ) (hm : m + 1 ≤ 2 * i) :
    |coefP lam i M| * (lam i) ^ m ≤ CB * (1 / 3 : ℝ) ^ i :=
  (abs_mul_pow_le_of_core h) i ((abs_coefP_mul_pow_le h) i M) hm

private theorem abs_coef_le_CB {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) : |coef lam i| ≤ CB := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · unfold coef; rw [head_zero, one_mul, abs_of_nonneg ((tail_nonneg h) 0)]; exact (tail_le_CB h) 0
  · have := abs_coef_mul_pow_le_geom h (i := i) (m := 0) (by omega)
    rw [pow_zero, mul_one] at this
    refine this.trans ?_
    have h13 : (1 / 3 : ℝ) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    unfold CB at *; nlinarith

private theorem abs_coefP_le_CB {lam : ℕ → ℝ} (h : KernelGood lam) (i M : ℕ) : |coefP lam i M| ≤ CB := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · unfold coefP; rw [head_zero, one_mul, abs_of_nonneg ((tailP_nonneg h) 0 M)]; exact (tailP_le_CB h) 0 M
  · have := abs_coefP_mul_pow_le_geom h (i := i) (m := 0) M (by omega)
    rw [pow_zero, mul_one] at this
    refine this.trans ?_
    have h13 : (1 / 3 : ℝ) ^ i ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    unfold CB at *; nlinarith

private theorem ratio_self (lam : ℕ → ℝ) {i : ℕ} (hi : lam i ≠ 0) : ratio lam i i = 1 := by
  unfold ratio; exact div_self (pow_ne_zero 2 hi)

private theorem coef_zero_mul_factor {lam : ℕ → ℝ} (h : KernelGood lam) : coef lam 0 * (1 - ratio lam 0 0) = 0 := by
  rw [ratio_self lam (h.ne_zero 0)]; ring

private theorem head_succ_eq {lam : ℕ → ℝ} (k : ℕ) :
    head lam (k + 1) = head (shift lam) k * (1 - ratio lam (k + 1) 0)⁻¹ := by
  unfold head
  exact prod_range_succ' (fun j => (1 - ratio lam (k + 1) j)⁻¹) k

private theorem coef_succ_mul_factor {lam : ℕ → ℝ} (h : KernelGood lam) (k : ℕ) :
    coef lam (k + 1) * (1 - ratio lam (k + 1) 0) = coef (shift lam) k := by
  have hr := four_le_ratio h (show 0 < k + 1 by omega)
  have hne : (1 - ratio lam (k + 1) 0) ≠ 0 := by linarith
  unfold coef
  rw [head_succ_eq, tail_shift]
  field_simp

private theorem coefP_succ_mul_factor {lam : ℕ → ℝ} (h : KernelGood lam) (k M : ℕ) :
    coefP lam (k + 1) M * (1 - ratio lam (k + 1) 0) = coefP (shift lam) k M := by
  have hr := four_le_ratio h (show 0 < k + 1 by omega)
  have hne : (1 - ratio lam (k + 1) 0) ≠ 0 := by linarith
  unfold coefP
  rw [head_succ_eq, tailP_shift]
  field_simp

private def es (u : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | N + 1, 0 => es u N 0
  | N + 1, n + 1 => es u N (n + 1) + u N * es u N n

section es

variable (u : ℕ → ℝ)

@[scoped simp] private theorem es_zero_zero : es u 0 0 = 1 := rfl
@[scoped simp] private theorem es_zero_succ (n : ℕ) : es u 0 (n + 1) = 0 := rfl
private theorem es_succ_zero (N : ℕ) : es u (N + 1) 0 = es u N 0 := rfl
private theorem es_succ_succ (N n : ℕ) : es u (N + 1) (n + 1) = es u N (n + 1) + u N * es u N n := rfl

@[scoped simp] private theorem es_right_zero : ∀ N, es u N 0 = 1
  | 0 => rfl
  | N + 1 => by rw [es_succ_zero]; exact es_right_zero N

private theorem es_eq_zero_of_lt : ∀ N n, N < n → es u N n = 0
  | 0, 0, h => absurd h (by omega)
  | 0, _ + 1, _ => rfl
  | N + 1, 0, h => absurd h (by omega)
  | N + 1, n + 1, h => by
    rw [es_succ_succ, es_eq_zero_of_lt N (n + 1) (by omega), es_eq_zero_of_lt N n (by omega)]
    ring

variable {u}

private theorem es_nonneg (hu : ∀ n, 0 ≤ u n) : ∀ N n, 0 ≤ es u N n
  | 0, 0 => by simp
  | 0, _ + 1 => by simp
  | N + 1, 0 => by rw [es_succ_zero]; exact es_nonneg hu N 0
  | N + 1, n + 1 => by
    rw [es_succ_succ]
    have h1 := es_nonneg hu N (n + 1)
    have h2 := es_nonneg hu N n
    have h3 := hu N
    positivity

private theorem es_le_succ (hu : ∀ n, 0 ≤ u n) (N n : ℕ) : es u N n ≤ es u (N + 1) n := by
  cases n with
  | zero => rw [es_succ_zero]
  | succ n =>
    rw [es_succ_succ]
    have := mul_nonneg (hu N) (es_nonneg hu N n)
    linarith

private theorem es_mono (hu : ∀ n, 0 ≤ u n) (n : ℕ) : Monotone (fun N => es u N n) :=
  monotone_nat_of_le_succ (fun N => es_le_succ hu N n)

private def esS (u : ℕ → ℝ) (N n : ℕ) : ℝ := ∑ M ∈ range N, (if n ≤ M then u M else 0)

private theorem esS_zero (n : ℕ) : esS u 0 n = 0 := by simp [esS]

private theorem esS_succ (N n : ℕ) : esS u (N + 1) n = esS u N n + (if n ≤ N then u N else 0) := by
  simp [esS, sum_range_succ]

private theorem esS_nonneg (hu : ∀ n, 0 ≤ u n) (N n : ℕ) : 0 ≤ esS u N n := by
  unfold esS
  apply sum_nonneg
  intro M _
  split_ifs
  · exact hu M
  · exact le_rfl

private theorem es_succ_le_esS_mul (hu : ∀ n, 0 ≤ u n) : ∀ N n, es u N (n + 1) ≤ esS u N n * es u N n := by
  intro N
  induction N with
  | zero => intro n; simp [esS_zero]
  | succ N ih =>
    intro n
    rw [es_succ_succ, esS_succ]
    by_cases hn : n ≤ N
    · rw [if_pos hn]
      have h1 := ih n
      have h2 := es_le_succ hu N n
      have h3 := esS_nonneg hu N n
      have h4 := hu N
      have h5 := es_nonneg hu N n
      have h6 : es u N n ≤ es u (N + 1) n := h2
      nlinarith [mul_le_mul_of_nonneg_left h6 h3, mul_le_mul_of_nonneg_left h6 h4]
    · rw [if_neg hn]
      have hz1 : es u N (n + 1) = 0 := es_eq_zero_of_lt u N (n + 1) (by omega)
      have hz2 : es u N n = 0 := es_eq_zero_of_lt u N n (by omega)
      rw [hz1, hz2]
      have := es_nonneg hu (N + 1) n
      have := esS_nonneg hu N n
      simp only [mul_zero, add_zero]
      positivity

private theorem esS_le_of_le (hhalf : ∀ n, u (n + 1) ≤ u n / 4) :
    ∀ N n, n ≤ N → esS u N n ≤ (4 / 3) * (u n - u N) := by
  intro N
  induction N with
  | zero => intro n hn; have : n = 0 := by omega
            subst this; rw [esS_zero]; simp
  | succ N ih =>
    intro n hn
    rw [esS_succ]
    rcases Nat.lt_or_ge N n with hlt | hle
    ·
      have hnN : n = N + 1 := by omega
      subst hnN
      have hz : esS u N (N + 1) = 0 := by
        unfold esS
        apply sum_eq_zero
        intro M hM
        rw [if_neg (by have := mem_range.1 hM; omega)]
      rw [hz, if_neg (by omega)]
      simp
    · rw [if_pos hle]
      have h1 := ih n hle
      have h2 := hhalf N
      linarith

private theorem esS_le (hu : ∀ n, 0 ≤ u n) (hhalf : ∀ n, u (n + 1) ≤ u n / 4) (N n : ℕ) :
    esS u N n ≤ (4 / 3) * u n := by
  by_cases hle : n ≤ N
  · have := esS_le_of_le hhalf N n hle
    have := hu N
    linarith
  · have hlt : N < n := not_le.mp hle
    have hz : esS u N n = 0 := by
      unfold esS
      apply sum_eq_zero
      intro M hM
      rw [if_neg (by have := mem_range.1 hM; omega)]
    rw [hz]
    have := hu n
    positivity

private def ebar (u : ℕ → ℝ) (n : ℕ) : ℝ := (4 / 3 : ℝ) ^ n * ∏ j ∈ range n, u j

private theorem ebar_zero : ebar u 0 = 1 := by simp [ebar]

private theorem ebar_succ (n : ℕ) : ebar u (n + 1) = (4 / 3) * u n * ebar u n := by
  simp only [ebar, prod_range_succ, pow_succ]; ring

private theorem ebar_nonneg (hu : ∀ n, 0 ≤ u n) (n : ℕ) : 0 ≤ ebar u n := by
  unfold ebar
  exact mul_nonneg (by positivity) (prod_nonneg (fun j _ => hu j))

private theorem es_le_ebar (hu : ∀ n, 0 ≤ u n) (hhalf : ∀ n, u (n + 1) ≤ u n / 4) (N : ℕ) :
    ∀ n, es u N n ≤ ebar u n := by
  intro n
  induction n with
  | zero => simp [ebar_zero]
  | succ n ih =>
    rw [ebar_succ]
    have h1 := es_succ_le_esS_mul hu N n
    have h2 := esS_le hu hhalf N n
    have h3 := es_nonneg hu N n
    have h4 : esS u N n * es u N n ≤ (4 / 3 * u n) * es u N n :=
      mul_le_mul_of_nonneg_right h2 h3
    have h5 : (4 / 3 * u n) * es u N n ≤ (4 / 3 * u n) * ebar u n :=
      mul_le_mul_of_nonneg_left ih (by have := hu n; positivity)
    calc es u N (n + 1) ≤ esS u N n * es u N n := h1
      _ ≤ (4 / 3 * u n) * es u N n := h4
      _ ≤ (4 / 3 * u n) * ebar u n := h5
      _ = 4 / 3 * u n * ebar u n := by ring

private theorem ebar_mul_eight_pow_le (hu : ∀ n, 0 ≤ u n) (hu16 : ∀ n, u n ≤ 1 / 16) (n : ℕ) :
    ebar u n * (8 : ℝ) ^ n ≤ (2 / 3 : ℝ) ^ n := by
  induction n with
  | zero => simp [ebar_zero]
  | succ n ih =>
    rw [ebar_succ, pow_succ, pow_succ]
    have h1 := hu n
    have h2 := hu16 n
    have h3 := ebar_nonneg hu n
    have h4 : (0 : ℝ) ≤ 8 ^ n := by positivity
    have h5 : 0 ≤ ebar u n * (8 : ℝ) ^ n := by positivity
    calc 4 / 3 * u n * ebar u n * ((8 : ℝ) ^ n * 8) = (ebar u n * 8 ^ n) * (4 / 3 * 8 * u n) := by ring
      _ ≤ (2 / 3 : ℝ) ^ n * (4 / 3 * 8 * (1 / 16)) := by
          apply mul_le_mul ih _ (by positivity) (by positivity)
          nlinarith
      _ = (2 / 3 : ℝ) ^ n * (2 / 3) := by norm_num

private def eLim (u : ℕ → ℝ) (n : ℕ) : ℝ := ⨆ N : ℕ, es u N n

private theorem es_bddAbove (hu : ∀ n, 0 ≤ u n) (hhalf : ∀ n, u (n + 1) ≤ u n / 4) (n : ℕ) :
    BddAbove (Set.range (fun N => es u N n)) :=
  ⟨ebar u n, by rintro _ ⟨N, rfl⟩; exact es_le_ebar hu hhalf N n⟩

private theorem es_le_eLim (hu : ∀ n, 0 ≤ u n) (hhalf : ∀ n, u (n + 1) ≤ u n / 4) (N n : ℕ) :
    es u N n ≤ eLim u n :=
  le_ciSup (es_bddAbove hu hhalf n) N

private theorem eLim_le_ebar (hu : ∀ n, 0 ≤ u n) (hhalf : ∀ n, u (n + 1) ≤ u n / 4) (n : ℕ) :
    eLim u n ≤ ebar u n :=
  ciSup_le (fun N => es_le_ebar hu hhalf N n)

private theorem eLim_nonneg (hu : ∀ n, 0 ≤ u n) (hhalf : ∀ n, u (n + 1) ≤ u n / 4) (n : ℕ) : 0 ≤ eLim u n :=
  (es_nonneg hu 0 n).trans (es_le_eLim hu hhalf 0 n)

private theorem tendsto_es (hu : ∀ n, 0 ≤ u n) (hhalf : ∀ n, u (n + 1) ≤ u n / 4) (n : ℕ) :
    Tendsto (fun N => es u N n) atTop (𝓝 (eLim u n)) :=
  tendsto_atTop_ciSup (es_mono hu n) (es_bddAbove hu hhalf n)

end es

private structure MasterGood (δ : ℝ) (Bs : ℕ → ℝ) (lam : ℕ → ℝ) : Prop where
  k5 : ∀ i, CB * Bs (3 * i + 3) * (lam i) ^ (3 * i + 3) * Real.exp (-(lam i * δ / 2)) ≤ (1 / 2 : ℝ) ^ i
  k3 : ∀ N, 1 ≤ N →
    (4 / 3 : ℝ) ^ (N + 1) * (∏ j ∈ range (N + 1), uOf lam j) * (8 : ℝ) ^ (N + 1) * Bs (3 * N + 3)
      * (lam (N - 1)) ^ (3 * N + 3) ≤ (1 / 2 : ℝ) ^ (N + 1)

private theorem MasterGood.tail_bound {δ : ℝ} {Bs : ℕ → ℝ} {lam : ℕ → ℝ} (hm : MasterGood δ Bs lam) {n : ℕ} (hn : 2 ≤ n) :
    ebar (uOf lam) n * (8 : ℝ) ^ n * Bs (3 * n) * (lam (n - 2)) ^ (3 * n) ≤ (1 / 2 : ℝ) ^ n := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have h := hm.k3 N (by omega)
  unfold ebar
  rw [show 3 * (N + 1) = 3 * N + 3 by ring, show N + 1 - 2 = N - 1 by omega]
  calc (4 / 3 : ℝ) ^ (N + 1) * (∏ j ∈ range (N + 1), uOf lam j) * (8 : ℝ) ^ (N + 1) * Bs (3 * N + 3)
        * (lam (N - 1)) ^ (3 * N + 3)
      ≤ (1 / 2 : ℝ) ^ (N + 1) := h

end OneVariableFactorization
p2m_reactivate "P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.OneVariableFactorization"

namespace OneVariableFactorization

open Finset Filter Topology

private theorem summable_CB_geom (k : ℕ) : Summable (fun i : ℕ => (CB * (1 / 3 : ℝ) ^ k) * (1 / 3 : ℝ) ^ i) :=
  (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

private theorem summable_CB_geom₀ : Summable (fun i : ℕ => CB * (1 / 3 : ℝ) ^ i) :=
  (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

private theorem summable_abs_coef_mul_pow {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) :
    Summable (fun i => |coef lam i| * (lam i) ^ m) := by
  rw [← summable_nat_add_iff (m + 1)]
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) (summable_CB_geom (m + 1))
  · have := h.pos (i + (m + 1)); positivity
  · have hb := abs_coef_mul_pow_le_geom h (i := i + (m + 1)) (m := m) (by omega)
    calc |coef lam (i + (m + 1))| * (lam (i + (m + 1))) ^ m ≤ CB * (1 / 3 : ℝ) ^ (i + (m + 1)) := hb
      _ = (CB * (1 / 3 : ℝ) ^ (m + 1)) * (1 / 3 : ℝ) ^ i := by rw [pow_add]; ring

private theorem CB_pos : 0 < CB := by unfold CB; norm_num

private theorem abs_coef_le_geom {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) : |coef lam i| ≤ CB * (1 / 3 : ℝ) ^ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa using abs_coef_le_CB h 0
  · have := abs_coef_mul_pow_le_geom h (i := i) (m := 0) (by omega)
    simpa using this

private theorem abs_coefP_le_geom {lam : ℕ → ℝ} (h : KernelGood lam) (i M : ℕ) :
    |coefP lam i M| ≤ CB * (1 / 3 : ℝ) ^ i := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simpa using abs_coefP_le_CB h 0 M
  · have := abs_coefP_mul_pow_le_geom h (i := i) (m := 0) M (by omega)
    simpa using this

private theorem summable_coef {lam : ℕ → ℝ} (h : KernelGood lam) : Summable (coef lam) :=
  Summable.of_norm_bounded summable_CB_geom₀ (fun i => by simpa using abs_coef_le_geom h i)

private theorem summable_coef_mul_sq_pow {lam : ℕ → ℝ} (h : KernelGood lam) (j : ℕ) :
    Summable (fun i => coef lam i * ((lam i) ^ 2) ^ j) := by
  refine Summable.of_norm_bounded (summable_abs_coef_mul_pow h (2 * j)) (fun i => ?_)
  have hp : 0 ≤ (lam i) ^ (2 * j) := by have := h.pos i; positivity
  rw [Real.norm_eq_abs, abs_mul, ← pow_mul, abs_of_nonneg hp]

private theorem KernelGood.strictMono {lam : ℕ → ℝ} (h : KernelGood lam) : StrictMono lam :=
  strictMono_nat_of_lt_succ (fun n => by have := h.double n; have := h.pos n; linarith)

private theorem nodes_injOn {lam : ℕ → ℝ} (h : KernelGood lam) (s : Finset ℕ) :
    Set.InjOn (fun j : ℕ => (lam j) ^ 2) (s : Set ℕ) := by
  intro a _ b _ hab
  simp only at hab
  have hfac : (lam a - lam b) * (lam a + lam b) = 0 := by
    have : (lam a - lam b) * (lam a + lam b) = (lam a) ^ 2 - (lam b) ^ 2 := by ring
    rw [this, hab, sub_self]
  rcases mul_eq_zero.1 hfac with h1 | h1
  · exact h.strictMono.injective (by linarith)
  · have := h.pos a; have := h.pos b; linarith

private theorem eval_zero_basisDivisor_eq {x y : ℝ} (hy : y ≠ 0) :
    Polynomial.eval 0 (Lagrange.basisDivisor x y) = (1 - x / y)⁻¹ := by
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
    Polynomial.eval_X]
  have h1 : (1 : ℝ) - x / y = (y - x) / y := by field_simp
  rw [h1, inv_div, show x - y = -(y - x) by ring, inv_neg, zero_sub, neg_mul_neg, div_eq_inv_mul]

private theorem eval_zero_basis_eq_coefP {lam : ℕ → ℝ} (h : KernelGood lam) (i K : ℕ) :
    Polynomial.eval 0 (Lagrange.basis (range (i + 1 + K)) (fun j => (lam j) ^ 2) i) = coefP lam i K := by
  unfold Lagrange.basis
  rw [Polynomial.eval_prod]

  set g : ℕ → ℝ := fun j => if j = i then 1 else (1 - ratio lam i j)⁻¹ with hg
  have hfac : ∀ j ∈ (range (i + 1 + K)).erase i,
      Polynomial.eval 0 (Lagrange.basisDivisor ((lam i) ^ 2) ((lam j) ^ 2)) = g j := by
    intro j hj
    have hji : j ≠ i := (mem_erase.1 hj).1
    rw [eval_zero_basisDivisor_eq (pow_ne_zero 2 (h.ne_zero j))]
    simp only [hg, if_neg hji, ratio]
  rw [prod_congr rfl hfac, prod_erase _ (by simp)]
  rw [prod_range_add, prod_range_succ]
  have hhead : ∏ j ∈ range i, g j = head lam i := by
    unfold head
    apply prod_congr rfl
    intro j hj
    have : j ≠ i := (mem_range.1 hj).ne
    simp only [hg, if_neg this]
  have hgi : g i = 1 := by simp [hg]
  have htail : ∏ k ∈ range K, g (i + 1 + k) = tailP lam i K := by
    unfold tailP
    apply prod_congr rfl
    intro k _
    have : i + 1 + k ≠ i := by omega
    simp only [hg, if_neg this, tf]
  show (∏ j ∈ range i, g j) * g i * ∏ k ∈ range K, g (i + 1 + k) = coefP lam i K
  rw [hhead, hgi, mul_one, htail]
  rfl

private theorem sum_coefP_eq_one {lam : ℕ → ℝ} (h : KernelGood lam) (M : ℕ) (hM : 1 ≤ M) :
    ∑ i ∈ range M, (if i < M then coefP lam i (M - 1 - i) else 0) = 1 := by
  have hs : (range M).Nonempty := ⟨0, mem_range.2 (by omega)⟩
  have hL := Lagrange.sum_basis (nodes_injOn h (range M)) hs
  have hev := congrArg (Polynomial.eval (0 : ℝ)) hL
  rw [Polynomial.eval_finsetSum, Polynomial.eval_one] at hev
  rw [← hev]
  apply sum_congr rfl
  intro i hi
  have hiM : i < M := mem_range.1 hi
  rw [if_pos hiM]
  obtain ⟨K, hK⟩ : ∃ K, M = i + 1 + K := ⟨M - 1 - i, by omega⟩
  have hK' : M - 1 - i = K := by omega
  rw [hK']
  subst hK
  exact (eval_zero_basis_eq_coefP h i K).symm

private theorem tsum_coef_eq_one {lam : ℕ → ℝ} (h : KernelGood lam) : ∑' i, coef lam i = 1 := by

  set F : ℕ → ℕ → ℝ := fun M i => if i < M then coefP lam i (M - 1 - i) else 0 with hF
  have hlim : ∀ i, Tendsto (fun M => F M i) atTop (𝓝 (coef lam i)) := by
    intro i
    have h1 : Tendsto (fun M => coefP lam i (M - (i + 1))) atTop (𝓝 (coef lam i)) :=
      (tendsto_coefP h i).comp (tendsto_sub_atTop_nat (i + 1))
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop i] with M hM
    simp only [hF, if_pos hM]
    congr 1
    omega
  have hbound : ∀ M, ∀ i, ‖F M i‖ ≤ CB * (1 / 3 : ℝ) ^ i := by
    intro M i
    simp only [hF]
    split_ifs
    · rw [Real.norm_eq_abs]; exact abs_coefP_le_geom h i _
    · simp only [norm_zero]; have := CB_pos; positivity
  have hT : Tendsto (fun M => ∑' i, F M i) atTop (𝓝 (∑' i, coef lam i)) :=
    tendsto_tsum_of_dominated_convergence summable_CB_geom₀ hlim (Eventually.of_forall hbound)
  have hconst : ∀ M, 1 ≤ M → ∑' i, F M i = 1 := by
    intro M hM
    rw [tsum_eq_sum (s := range M)]
    · exact sum_coefP_eq_one h M hM
    · intro i hi
      simp only [hF, if_neg (fun hlt => hi (mem_range.2 hlt))]
  have hT1 : Tendsto (fun M => ∑' i, F M i) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with M hM
    exact (hconst M hM).symm
  exact (tendsto_nhds_unique hT hT1)

private theorem coef_shift_mul_pow {lam : ℕ → ℝ} (h : KernelGood lam) (j k : ℕ) :
    coef (shift lam) k * ((shift lam k) ^ 2) ^ j
      = coef lam (k + 1) * ((lam (k + 1)) ^ 2) ^ j
        - (1 / (lam 0) ^ 2) * (coef lam (k + 1) * ((lam (k + 1)) ^ 2) ^ (j + 1)) := by
  have hC3 := coef_succ_mul_factor h k
  have h0 : (lam 0) ^ 2 ≠ 0 := pow_ne_zero 2 (h.ne_zero 0)
  show coef (shift lam) k * ((lam (k + 1)) ^ 2) ^ j = _
  rw [← hC3]
  unfold ratio
  field_simp
  ring

private theorem moment_eq {lam : ℕ → ℝ} (h : KernelGood lam) :
    ∀ j : ℕ, ∑' i, coef lam i * ((lam i) ^ 2) ^ j = if j = 0 then 1 else 0 := by

  suffices H : ∀ j : ℕ, ∀ mu : ℕ → ℝ, KernelGood mu → ∑' i, coef mu i * ((mu i) ^ 2) ^ j = if j = 0 then 1 else 0 by
    exact fun j => H j lam h
  intro j
  induction j with
  | zero =>
    intro mu hmu
    simp only [pow_zero, mul_one, if_true]
    exact tsum_coef_eq_one hmu
  | succ j ih =>
    intro mu hmu
    have hmu' := hmu.shift
    have hf := summable_coef_mul_sq_pow hmu j
    have hg := summable_coef_mul_sq_pow hmu (j + 1)
    have hIH := ih mu hmu
    have hIH' := ih (shift mu) hmu'

    have hterm : ∀ k, coef (shift mu) k * ((shift mu k) ^ 2) ^ j
        = (fun i => coef mu i * ((mu i) ^ 2) ^ j) (k + 1)
          - (1 / (mu 0) ^ 2) * (fun i => coef mu i * ((mu i) ^ 2) ^ (j + 1)) (k + 1) :=
      fun k => coef_shift_mul_pow hmu j k
    have hf1 : Summable (fun k => (fun i => coef mu i * ((mu i) ^ 2) ^ j) (k + 1)) :=
      (summable_nat_add_iff 1).2 hf
    have hg1 : Summable (fun k => (fun i => coef mu i * ((mu i) ^ 2) ^ (j + 1)) (k + 1)) :=
      (summable_nat_add_iff 1).2 hg
    have hsum : ∑' k, coef (shift mu) k * ((shift mu k) ^ 2) ^ j
        = (∑' k, (fun i => coef mu i * ((mu i) ^ 2) ^ j) (k + 1))
          - (1 / (mu 0) ^ 2) * ∑' k, (fun i => coef mu i * ((mu i) ^ 2) ^ (j + 1)) (k + 1) := by
      simp_rw [hterm]
      rw [hf1.tsum_sub (hg1.mul_left _), hg1.tsum_mul_left]
    have hA := hf.tsum_eq_zero_add
    have hB := hg.tsum_eq_zero_add
    rw [hIH'] at hsum
    rw [hIH] at hA
    have h0 : (mu 0) ^ 2 ≠ 0 := pow_ne_zero 2 (hmu.ne_zero 0)

    set Mj1 := ∑' i, coef mu i * ((mu i) ^ 2) ^ (j + 1) with hMj1
    simp only [Nat.succ_ne_zero, if_false]

    have hx : (1 / (mu 0) ^ 2) * (coef mu 0 * ((mu 0) ^ 2) ^ (j + 1)) = coef mu 0 * ((mu 0) ^ 2) ^ j := by
      calc (1 / (mu 0) ^ 2) * (coef mu 0 * ((mu 0) ^ 2) ^ (j + 1))
          = coef mu 0 * ((mu 0) ^ 2) ^ j * ((mu 0) ^ 2 * (1 / (mu 0) ^ 2)) := by ring
        _ = coef mu 0 * ((mu 0) ^ 2) ^ j := by rw [mul_one_div_cancel h0, mul_one]
    have hS1 : ∑' k, (fun i => coef mu i * ((mu i) ^ 2) ^ j) (k + 1)
        = (if j = 0 then (1 : ℝ) else 0) - coef mu 0 * ((mu 0) ^ 2) ^ j := by
      simp only at hA ⊢; linarith
    have hS2 : ∑' k, (fun i => coef mu i * ((mu i) ^ 2) ^ (j + 1)) (k + 1)
        = Mj1 - coef mu 0 * ((mu 0) ^ 2) ^ (j + 1) := by
      simp only at hB ⊢; linarith
    rw [hS1, hS2, mul_sub, hx] at hsum
    have hM : (1 / (mu 0) ^ 2) * Mj1 = 0 := by linarith
    rcases mul_eq_zero.1 hM with hbad | hgood
    · exact absurd hbad (by positivity)
    · exact hgood

private theorem tsum_coef_mul_pow_even_eq_zero {lam : ℕ → ℝ} (h : KernelGood lam) {j : ℕ} (hj : 1 ≤ j) :
    ∑' i, coef lam i * (lam i) ^ (2 * j) = 0 := by
  have := moment_eq h j
  rw [if_neg (by omega)] at this
  simpa [pow_mul] using this

private def kterm (lam : ℕ → ℝ) (m i : ℕ) (t : ℝ) : ℝ :=
  coef lam i * (lam i / 2) * (if t < 0 then (lam i) ^ m else (-(lam i)) ^ m) * Real.exp (-(lam i * |t|))

private def ktermR (lam : ℕ → ℝ) (m i : ℕ) (t : ℝ) : ℝ :=
  coef lam i * (lam i / 2) * (-(lam i)) ^ m * Real.exp (-(lam i * |t|))

private def ktermL (lam : ℕ → ℝ) (m i : ℕ) (t : ℝ) : ℝ :=
  coef lam i * (lam i / 2) * (lam i) ^ m * Real.exp (-(lam i * |t|))

private def kerD (lam : ℕ → ℝ) (m : ℕ) (t : ℝ) : ℝ := ∑' i, kterm lam m i t
private def kerR (lam : ℕ → ℝ) (m : ℕ) (t : ℝ) : ℝ := ∑' i, ktermR lam m i t
private def kerL (lam : ℕ → ℝ) (m : ℕ) (t : ℝ) : ℝ := ∑' i, ktermL lam m i t

private def ker (lam : ℕ → ℝ) : ℝ → ℝ := kerD lam 0

private def kb (lam : ℕ → ℝ) (m i : ℕ) : ℝ := |coef lam i| * (lam i) ^ (m + 1)

private theorem summable_kb {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) : Summable (kb lam m) :=
  summable_abs_coef_mul_pow h (m + 1)

private theorem kb_nonneg {lam : ℕ → ℝ} (h : KernelGood lam) (m i : ℕ) : 0 ≤ kb lam m i := by
  unfold kb; have := h.pos i; positivity

private theorem abs_term_le {lam : ℕ → ℝ} (h : KernelGood lam) (m i : ℕ) {s : ℝ} (hs : |s| ≤ (lam i) ^ m) (t : ℝ) :
    |coef lam i * (lam i / 2) * s * Real.exp (-(lam i * |t|))| ≤ kb lam m i := by
  have hl := h.pos i
  have he : Real.exp (-(lam i * |t|)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ lam i * |t| := by positivity
    linarith
  have he0 : 0 ≤ Real.exp (-(lam i * |t|)) := (Real.exp_pos _).le
  unfold kb
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < lam i / 2), abs_of_nonneg he0]
  have hc : 0 ≤ |coef lam i| := abs_nonneg _
  have hs0 : 0 ≤ |s| := abs_nonneg _
  calc |coef lam i| * (lam i / 2) * |s| * Real.exp (-(lam i * |t|))
      ≤ |coef lam i| * (lam i / 2) * (lam i) ^ m * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) he he0 (by positivity)
    _ ≤ |coef lam i| * (lam i) ^ (m + 1) := by
        rw [mul_one, pow_succ]
        have hm0 : 0 ≤ (lam i) ^ m := by positivity
        nlinarith [mul_nonneg hc hm0]

private theorem abs_kterm_le {lam : ℕ → ℝ} (h : KernelGood lam) (m i : ℕ) (t : ℝ) : |kterm lam m i t| ≤ kb lam m i := by
  unfold kterm
  apply abs_term_le h m i _ t
  split_ifs
  · rw [abs_of_nonneg (by have := h.pos i; positivity)]
  · rw [abs_pow, abs_neg, abs_of_pos (h.pos i)]

private theorem abs_ktermR_le {lam : ℕ → ℝ} (h : KernelGood lam) (m i : ℕ) (t : ℝ) : |ktermR lam m i t| ≤ kb lam m i := by
  unfold ktermR
  apply abs_term_le h m i _ t
  rw [abs_pow, abs_neg, abs_of_pos (h.pos i)]

private theorem abs_ktermL_le {lam : ℕ → ℝ} (h : KernelGood lam) (m i : ℕ) (t : ℝ) : |ktermL lam m i t| ≤ kb lam m i := by
  unfold ktermL
  apply abs_term_le h m i _ t
  rw [abs_of_nonneg (by have := h.pos i; positivity)]

private theorem summable_kterm {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) (t : ℝ) : Summable (fun i => kterm lam m i t) :=
  Summable.of_norm_bounded (summable_kb h m) (fun i => by rw [Real.norm_eq_abs]; exact abs_kterm_le h m i t)

private theorem summable_ktermR {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) (t : ℝ) : Summable (fun i => ktermR lam m i t) :=
  Summable.of_norm_bounded (summable_kb h m) (fun i => by rw [Real.norm_eq_abs]; exact abs_ktermR_le h m i t)

private theorem summable_ktermL {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) (t : ℝ) : Summable (fun i => ktermL lam m i t) :=
  Summable.of_norm_bounded (summable_kb h m) (fun i => by rw [Real.norm_eq_abs]; exact abs_ktermL_le h m i t)

private theorem kterm_eq_ktermR (lam : ℕ → ℝ) (m i : ℕ) {t : ℝ} (ht : 0 ≤ t) : kterm lam m i t = ktermR lam m i t := by
  unfold kterm ktermR; rw [if_neg (not_lt.2 ht)]

private theorem kterm_eq_ktermL (lam : ℕ → ℝ) (m i : ℕ) {t : ℝ} (ht : t < 0) : kterm lam m i t = ktermL lam m i t := by
  unfold kterm ktermL; rw [if_pos ht]

private theorem kerD_eq_kerR (lam : ℕ → ℝ) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) : kerD lam m t = kerR lam m t := by
  unfold kerD kerR; simp_rw [kterm_eq_ktermR lam m _ ht]

private theorem kerD_eq_kerL_of_neg (lam : ℕ → ℝ) (m : ℕ) {t : ℝ} (ht : t < 0) : kerD lam m t = kerL lam m t := by
  unfold kerD kerL; simp_rw [kterm_eq_ktermL lam m _ ht]

private theorem kerR_zero_eq_kerL_zero {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) : kerR lam m 0 = kerL lam m 0 := by
  unfold kerR kerL ktermR ktermL
  rcases Nat.even_or_odd m with hev | hodd
  · simp_rw [hev.neg_pow]
  ·
    obtain ⟨j, rfl⟩ := hodd
    have hL : ∑' i, coef lam i * (lam i / 2) * (lam i) ^ (2 * j + 1) * Real.exp (-(lam i * |(0 : ℝ)|)) = 0 := by
      simp only [abs_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
      have hz := tsum_coef_mul_pow_even_eq_zero h (j := j + 1) (by omega)
      have hrew : ∀ i, coef lam i * (lam i / 2) * (lam i) ^ (2 * j + 1)
          = (1 / 2 : ℝ) * (coef lam i * (lam i) ^ (2 * (j + 1))) := by
        intro i; ring
      simp_rw [hrew]
      rw [tsum_mul_left, hz, mul_zero]
    have hR : ∀ i, coef lam i * (lam i / 2) * (-(lam i)) ^ (2 * j + 1) * Real.exp (-(lam i * |(0 : ℝ)|))
        = -(coef lam i * (lam i / 2) * (lam i) ^ (2 * j + 1) * Real.exp (-(lam i * |(0 : ℝ)|))) := by
      intro i
      rw [(odd_two_mul_add_one j).neg_pow]
      ring
    simp_rw [hR]
    rw [tsum_neg, hL, neg_zero]

private theorem kerD_eq_kerL {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) {t : ℝ} (ht : t ≤ 0) : kerD lam m t = kerL lam m t := by
  rcases ht.lt_or_eq with hlt | rfl
  · exact kerD_eq_kerL_of_neg lam m hlt
  · rw [kerD_eq_kerR lam m le_rfl]; exact kerR_zero_eq_kerL_zero h m

private theorem continuous_ktermR (lam : ℕ → ℝ) (m i : ℕ) : Continuous (ktermR lam m i) := by
  unfold ktermR; fun_prop

private theorem continuous_ktermL (lam : ℕ → ℝ) (m i : ℕ) : Continuous (ktermL lam m i) := by
  unfold ktermL; fun_prop

private theorem continuous_kerR {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) : Continuous (kerR lam m) := by
  unfold kerR
  exact continuous_tsum (fun i => continuous_ktermR lam m i) (summable_kb h m)
    (fun i t => by rw [Real.norm_eq_abs]; exact abs_ktermR_le h m i t)

private theorem continuous_kerL {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) : Continuous (kerL lam m) := by
  unfold kerL
  exact continuous_tsum (fun i => continuous_ktermL lam m i) (summable_kb h m)
    (fun i t => by rw [Real.norm_eq_abs]; exact abs_ktermL_le h m i t)

private theorem continuous_kerD {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) : Continuous (kerD lam m) := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  ·
    have hev : kerD lam m =ᶠ[𝓝 t] kerL lam m := by
      filter_upwards [Iio_mem_nhds hneg] with s hs
      exact kerD_eq_kerL_of_neg lam m hs
    exact ((continuous_kerL h m).continuousAt).congr hev.symm
  ·
    rw [continuousAt_iff_continuous_left_right]
    constructor
    · have hc : ContinuousWithinAt (kerL lam m) (Set.Iic 0) 0 := (continuous_kerL h m).continuousWithinAt
      refine hc.congr (fun s hs => kerD_eq_kerL h m hs) (kerD_eq_kerL h m le_rfl)
    · have hc : ContinuousWithinAt (kerR lam m) (Set.Ici 0) 0 := (continuous_kerR h m).continuousWithinAt
      refine hc.congr (fun s hs => kerD_eq_kerR lam m hs) (kerD_eq_kerR lam m le_rfl)
  · have hev : kerD lam m =ᶠ[𝓝 t] kerR lam m := by
      filter_upwards [Ioi_mem_nhds hpos] with s hs
      exact kerD_eq_kerR lam m hs.le
    exact ((continuous_kerR h m).continuousAt).congr hev.symm

end OneVariableFactorization
p2m_reactivate "P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.OneVariableFactorization"

namespace OneVariableFactorization

open Filter Topology

private theorem hasDerivAt_ktermR_of_pos {lam : ℕ → ℝ} (m i : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (ktermR lam m i) (ktermR lam (m + 1) i y) y := by
  set K : ℝ := coef lam i * (lam i / 2) * (-(lam i)) ^ m with hK
  have h1 : HasDerivAt (fun s : ℝ => -(lam i * s)) (-(lam i)) y := by
    have h__af := ((hasDerivAt_id y).const_mul (lam i)).neg
    simp at h__af
    exact h__af
  have hd : HasDerivAt (fun s : ℝ => K * Real.exp (-(lam i * s))) (K * (Real.exp (-(lam i * y)) * -(lam i))) y :=
    h1.exp.const_mul K
  have hev : ktermR lam m i =ᶠ[𝓝 y] (fun s : ℝ => K * Real.exp (-(lam i * s))) := by
    filter_upwards [Ioi_mem_nhds hy] with s hs
    have hs' : (0 : ℝ) < s := hs
    simp only [ktermR, hK, abs_of_pos hs']
  have hval : ktermR lam (m + 1) i y = K * (Real.exp (-(lam i * y)) * -(lam i)) := by
    simp only [ktermR, hK, abs_of_pos hy, pow_succ]
    ring
  rw [hval]
  exact hd.congr_of_eventuallyEq hev

private theorem hasDerivAt_ktermL_of_neg {lam : ℕ → ℝ} (m i : ℕ) {y : ℝ} (hy : y < 0) :
    HasDerivAt (ktermL lam m i) (ktermL lam (m + 1) i y) y := by
  set K : ℝ := coef lam i * (lam i / 2) * (lam i) ^ m with hK
  have h1 : HasDerivAt (fun s : ℝ => lam i * s) (lam i) y := by
    simpa using (hasDerivAt_id y).const_mul (lam i)
  have hd : HasDerivAt (fun s : ℝ => K * Real.exp (lam i * s)) (K * (Real.exp (lam i * y) * lam i)) y :=
    h1.exp.const_mul K
  have hev : ktermL lam m i =ᶠ[𝓝 y] (fun s : ℝ => K * Real.exp (lam i * s)) := by
    filter_upwards [Iio_mem_nhds hy] with s hs
    have hs' : s < 0 := hs
    simp only [ktermL, hK, abs_of_neg hs', mul_neg, neg_neg]
  have hval : ktermL lam (m + 1) i y = K * (Real.exp (lam i * y) * lam i) := by
    simp only [ktermL, hK, abs_of_neg hy, mul_neg, neg_neg, pow_succ]
    ring
  rw [hval]
  exact hd.congr_of_eventuallyEq hev

private theorem hasDerivAt_kerR_of_pos {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (kerR lam m) (kerR lam (m + 1) y) y := by
  show HasDerivAt (fun z => ∑' i, ktermR lam m i z) (∑' i, ktermR lam (m + 1) i y) y
  refine hasDerivAt_tsum_of_isPreconnected (summable_kb h (m + 1)) isOpen_Ioi isPreconnected_Ioi
    (fun i s hs => hasDerivAt_ktermR_of_pos m i (Set.mem_Ioi.1 hs))
    (fun i s _ => by rw [Real.norm_eq_abs]; exact abs_ktermR_le h (m + 1) i s)
    (Set.mem_Ioi.2 one_pos) (summable_ktermR h m 1) (Set.mem_Ioi.2 hy)

private theorem hasDerivAt_kerL_of_neg {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) {y : ℝ} (hy : y < 0) :
    HasDerivAt (kerL lam m) (kerL lam (m + 1) y) y := by
  show HasDerivAt (fun z => ∑' i, ktermL lam m i z) (∑' i, ktermL lam (m + 1) i y) y
  refine hasDerivAt_tsum_of_isPreconnected (summable_kb h (m + 1)) isOpen_Iio isPreconnected_Iio
    (fun i s hs => hasDerivAt_ktermL_of_neg m i (Set.mem_Iio.1 hs))
    (fun i s _ => by rw [Real.norm_eq_abs]; exact abs_ktermL_le h (m + 1) i s)
    (Set.mem_Iio.2 (by norm_num)) (summable_ktermL h m (-1)) (Set.mem_Iio.2 hy)

private theorem hasDerivAt_kerD_of_ne {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (kerD lam m) (kerD lam (m + 1) y) y := by
  rcases lt_or_gt_of_ne hy with hneg | hpos
  · have hev : kerD lam m =ᶠ[𝓝 y] kerL lam m := by
      filter_upwards [Iio_mem_nhds hneg] with s hs
      exact kerD_eq_kerL_of_neg lam m hs
    rw [kerD_eq_kerL_of_neg lam (m + 1) hneg]
    exact (hasDerivAt_kerL_of_neg h m hneg).congr_of_eventuallyEq hev
  · have hev : kerD lam m =ᶠ[𝓝 y] kerR lam m := by
      filter_upwards [Ioi_mem_nhds hpos] with s hs
      exact kerD_eq_kerR lam m (le_of_lt hs)
    rw [kerD_eq_kerR lam (m + 1) hpos.le]
    exact (hasDerivAt_kerR_of_pos h m hpos).congr_of_eventuallyEq hev

private theorem hasDerivAt_kerD {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) (y : ℝ) :
    HasDerivAt (kerD lam m) (kerD lam (m + 1) y) y := by
  by_cases hy : y = 0
  · subst hy
    exact hasDerivAt_of_hasDerivAt_of_ne (fun s hs => hasDerivAt_kerD_of_ne h m hs)
      (continuous_kerD h m).continuousAt (continuous_kerD h (m + 1)).continuousAt
  · exact hasDerivAt_kerD_of_ne h m hy

private theorem deriv_kerD {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) : deriv (kerD lam m) = kerD lam (m + 1) := by
  funext y
  exact (hasDerivAt_kerD h m y).deriv

private theorem differentiable_kerD {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) : Differentiable ℝ (kerD lam m) :=
  fun y => (hasDerivAt_kerD h m y).differentiableAt

private theorem iteratedDeriv_ker {lam : ℕ → ℝ} (h : KernelGood lam) : ∀ m : ℕ, iteratedDeriv m (ker lam) = kerD lam m
  | 0 => by rw [iteratedDeriv_zero]; rfl
  | m + 1 => by rw [iteratedDeriv_succ, iteratedDeriv_ker h m, deriv_kerD h m]

private theorem contDiff_ker {lam : ℕ → ℝ} (h : KernelGood lam) : ContDiff ℝ (⊤ : ℕ∞) (ker lam) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [iteratedDeriv_ker h m]
  exact differentiable_kerD h m

private theorem deriv_deriv_ker {lam : ℕ → ℝ} (h : KernelGood lam) : deriv (deriv (ker lam)) = kerD lam 2 := by
  have h0 : deriv (ker lam) = kerD lam 1 := deriv_kerD h 0
  rw [h0, deriv_kerD h 1]

private theorem kterm_step (lam : ℕ → ℝ) (i : ℕ) (t : ℝ) :
    kterm lam 0 i t - uOf lam 0 * kterm lam 2 i t
      = coef lam i * (1 - ratio lam i 0) * (lam i / 2) * Real.exp (-(lam i * |t|)) := by
  unfold kterm uOf ratio
  split_ifs <;> ring

private theorem kterm_step_zero {lam : ℕ → ℝ} (h : KernelGood lam) (t : ℝ) :
    kterm lam 0 0 t - uOf lam 0 * kterm lam 2 0 t = 0 := by
  rw [kterm_step, coef_zero_mul_factor h, zero_mul, zero_mul]

private theorem kterm_step_succ {lam : ℕ → ℝ} (h : KernelGood lam) (k : ℕ) (t : ℝ) :
    kterm lam 0 (k + 1) t - uOf lam 0 * kterm lam 2 (k + 1) t = kterm (shift lam) 0 k t := by
  rw [kterm_step, coef_succ_mul_factor h k]
  simp only [kterm, shift, pow_zero, ite_self, mul_one]

private theorem ker_step {lam : ℕ → ℝ} (h : KernelGood lam) :
    (fun t => ker lam t - uOf lam 0 * kerD lam 2 t) = ker (shift lam) := by
  funext t
  have hs0 := summable_kterm h 0 t
  have hs2 := summable_kterm h 2 t
  have hcomb : Summable (fun i => kterm lam 0 i t - uOf lam 0 * kterm lam 2 i t) := hs0.sub (hs2.mul_left _)
  calc ker lam t - uOf lam 0 * kerD lam 2 t
      = ∑' i, (kterm lam 0 i t - uOf lam 0 * kterm lam 2 i t) := by
        unfold ker kerD
        rw [hs0.tsum_sub (hs2.mul_left _), tsum_mul_left]
    _ = (kterm lam 0 0 t - uOf lam 0 * kterm lam 2 0 t)
          + ∑' k, (kterm lam 0 (k + 1) t - uOf lam 0 * kterm lam 2 (k + 1) t) := hcomb.tsum_eq_zero_add
    _ = ker (shift lam) t := by
        rw [kterm_step_zero h, zero_add]
        unfold ker kerD
        simp_rw [kterm_step_succ h]

private def _root_.OneVariableFactorization.shiftN : ℕ → (ℕ → ℝ) → (ℕ → ℝ)
  | 0, lam => lam
  | N + 1, lam => shift (shiftN N lam)

p2m_export "OneVariableFactorization" "shiftN"
private theorem shiftN_zero (lam : ℕ → ℝ) : shiftN 0 lam = lam := rfl

private theorem shiftN_succ (N : ℕ) (lam : ℕ → ℝ) : shiftN (N + 1) lam = shift (shiftN N lam) := rfl

private theorem shiftN_apply (lam : ℕ → ℝ) : ∀ N k : ℕ, shiftN N lam k = lam (k + N)
  | 0, k => by simp [shiftN]
  | N + 1, k => by
    rw [shiftN_succ]
    show shiftN N lam (k + 1) = lam (k + (N + 1))
    rw [shiftN_apply lam N (k + 1)]
    congr 1
    omega

private theorem KernelGood.shiftN {lam : ℕ → ℝ} (h : KernelGood lam) : ∀ N : ℕ, KernelGood (OneVariableFactorization.shiftN N lam)
  | 0 => h
  | N + 1 => (KernelGood.shiftN h N).shift

private theorem uOf_shiftN_zero (lam : ℕ → ℝ) (N : ℕ) : uOf (shiftN N lam) 0 = uOf lam N := by
  unfold uOf
  rw [shiftN_apply, Nat.zero_add]

private theorem uOf_one_div (a : ℕ → ℝ) (N : ℕ) (ha : a N ≠ 0) : uOf (fun n => 1 / a n) N = (a N) ^ 2 := by
  unfold uOf
  field_simp

private theorem ker_prod {lam : ℕ → ℝ} (h : KernelGood lam) (P : ℕ → ℝ → ℝ) (hP0 : P 0 = ker lam)
    (hPs : ∀ N, P (N + 1) = fun t => P N t - uOf lam N * deriv (deriv (P N)) t) :
    ∀ N, P N = ker (shiftN N lam)
  | 0 => hP0
  | N + 1 => by
    have hμ : KernelGood (shiftN N lam) := h.shiftN N
    rw [hPs N, ker_prod h P hP0 hPs N, deriv_deriv_ker hμ, ← uOf_shiftN_zero lam N, shiftN_succ]
    exact ker_step hμ

end OneVariableFactorization
p2m_reactivate "P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.OneVariableFactorization"

namespace OneVariableFactorization

open Filter Topology

private theorem summable_abs_coef {lam : ℕ → ℝ} (h : KernelGood lam) : Summable (fun i => |coef lam i|) :=
  (summable_coef h).abs

private theorem summable_norm_kterm {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) (t : ℝ) :
    Summable (fun i => ‖kterm lam m i t‖) := by
  simpa only [Real.norm_eq_abs] using (summable_kterm h m t).abs

private theorem tsum_abs_coef_le {lam : ℕ → ℝ} (h : KernelGood lam) : ∑' i, |coef lam i| ≤ CB * (3 / 2) := by
  have hg : ∑' i : ℕ, CB * (1 / 3 : ℝ) ^ i = CB * (3 / 2) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    ring
  rw [← hg]
  exact Summable.tsum_le_tsum (fun i => abs_coef_le_geom h i) (summable_abs_coef h) summable_CB_geom₀

private def wterm (lam : ℕ → ℝ) (r : ℝ) (m i : ℕ) : ℝ := |coef lam i| * (lam i) ^ (m + 1) * Real.exp (-(lam i * r))

private def W (lam : ℕ → ℝ) (r : ℝ) (m : ℕ) : ℝ := ∑' i, wterm lam r m i

private theorem wterm_nonneg {lam : ℕ → ℝ} (h : KernelGood lam) (r : ℝ) (m i : ℕ) : 0 ≤ wterm lam r m i := by
  unfold wterm; have := h.pos i; positivity

private theorem wterm_le_kb {lam : ℕ → ℝ} (h : KernelGood lam) {r : ℝ} (hr : 0 ≤ r) (m i : ℕ) : wterm lam r m i ≤ kb lam m i := by
  unfold wterm kb
  have hl := h.pos i
  have he : Real.exp (-(lam i * r)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have : 0 ≤ lam i * r := by positivity
    linarith
  have h0 : 0 ≤ |coef lam i| * (lam i) ^ (m + 1) := by positivity
  calc |coef lam i| * (lam i) ^ (m + 1) * Real.exp (-(lam i * r)) ≤ |coef lam i| * (lam i) ^ (m + 1) * 1 :=
        mul_le_mul_of_nonneg_left he h0
    _ = |coef lam i| * (lam i) ^ (m + 1) := mul_one _

private theorem summable_wterm {lam : ℕ → ℝ} (h : KernelGood lam) {r : ℝ} (hr : 0 ≤ r) (m : ℕ) : Summable (wterm lam r m) :=
  Summable.of_nonneg_of_le (wterm_nonneg h r m) (wterm_le_kb h hr m) (summable_kb h m)

private theorem W_nonneg {lam : ℕ → ℝ} (h : KernelGood lam) (r : ℝ) (m : ℕ) : 0 ≤ W lam r m :=
  tsum_nonneg (wterm_nonneg h r m)

private theorem W_mono {lam : ℕ → ℝ} (h : KernelGood lam) {r : ℝ} (hr : 0 ≤ r) {m m' : ℕ} (hmm' : m ≤ m') :
    W lam r m ≤ W lam r m' := by
  unfold W
  refine Summable.tsum_le_tsum (fun i => ?_) (summable_wterm h hr m) (summable_wterm h hr m')
  unfold wterm
  have h1 := h.one_le i
  have hp : (lam i) ^ (m + 1) ≤ (lam i) ^ (m' + 1) := pow_le_pow_right₀ h1 (by omega)
  have he : 0 ≤ Real.exp (-(lam i * r)) := (Real.exp_pos _).le
  have hc : 0 ≤ |coef lam i| := abs_nonneg _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hc) he

private theorem abs_kterm_le_wterm {lam : ℕ → ℝ} (h : KernelGood lam) (m i : ℕ) {r t : ℝ} (hrt : r ≤ |t|) :
    |kterm lam m i t| ≤ wterm lam r m i := by
  have hl := h.pos i
  have hsign : |(if t < 0 then (lam i) ^ m else (-(lam i)) ^ m)| = (lam i) ^ m := by
    split_ifs
    · exact abs_of_nonneg (by positivity)
    · rw [abs_pow, abs_neg, abs_of_pos hl]
  have he : Real.exp (-(lam i * |t|)) ≤ Real.exp (-(lam i * r)) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hrt hl.le
    linarith
  have he0 : 0 ≤ Real.exp (-(lam i * |t|)) := (Real.exp_pos _).le
  unfold kterm wterm
  rw [abs_mul, abs_mul, abs_mul, hsign, abs_of_nonneg he0, abs_of_pos (by positivity : (0 : ℝ) < lam i / 2)]
  have hc : 0 ≤ |coef lam i| := abs_nonneg _
  have hpm : 0 ≤ (lam i) ^ m := by positivity
  have hA : |coef lam i| * (lam i / 2) * (lam i) ^ m ≤ |coef lam i| * (lam i) ^ (m + 1) := by
    rw [pow_succ]
    have : (lam i / 2) * (lam i) ^ m ≤ (lam i) ^ m * lam i := by nlinarith
    calc |coef lam i| * (lam i / 2) * (lam i) ^ m = |coef lam i| * ((lam i / 2) * (lam i) ^ m) := by ring
      _ ≤ |coef lam i| * ((lam i) ^ m * lam i) := mul_le_mul_of_nonneg_left this hc
  exact mul_le_mul hA he he0 (by positivity)

private theorem abs_kerD_le_W {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ |t|) :
    |kerD lam m t| ≤ W lam r m := by
  have hs : Summable (fun i => ‖kterm lam m i t‖) := summable_norm_kterm h m t
  calc |kerD lam m t| = ‖∑' i, kterm lam m i t‖ := by rw [Real.norm_eq_abs]; rfl
    _ ≤ ∑' i, ‖kterm lam m i t‖ := norm_tsum_le_tsum_norm hs
    _ ≤ W lam r m :=
        Summable.tsum_le_tsum (fun i => by rw [Real.norm_eq_abs]; exact abs_kterm_le_wterm h m i hrt) hs
          (summable_wterm h hr m)

private theorem abs_mul_kerD_le {lam : ℕ → ℝ} (h : KernelGood lam) (m : ℕ) {g : ℝ → ℝ} {B r : ℝ} (hr : 0 ≤ r)
    (hg0 : ∀ t, |t| < r → g t = 0) (hgB : ∀ t, |g t| ≤ B) (t : ℝ) :
    |g t * kerD lam m t| ≤ B * W lam r m := by
  rw [abs_mul]
  by_cases ht : |t| < r
  · rw [hg0 t ht, abs_zero, zero_mul]
    have hB : 0 ≤ B := (abs_nonneg _).trans (hgB t)
    exact mul_nonneg hB (W_nonneg h r m)
  · push Not at ht
    exact mul_le_mul (hgB t) (abs_kerD_le_W h m hr ht) (abs_nonneg _) ((abs_nonneg _).trans (hgB t))

private theorem norm_kterm0_le {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) (t : ℝ) :
    ‖kterm lam 0 i t‖ ≤ kb lam 0 i * Real.exp (-(lam 0 * |t|)) := by
  have hl := h.pos i
  have hmono : lam 0 ≤ lam i := h.mono (Nat.zero_le i)
  have he : Real.exp (-(lam i * |t|)) ≤ Real.exp (-(lam 0 * |t|)) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right hmono (abs_nonneg t)
    linarith
  rw [Real.norm_eq_abs]
  unfold kterm kb
  simp only [pow_zero, ite_self, mul_one, zero_add, pow_one]
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < lam i / 2), abs_of_nonneg (Real.exp_pos _).le]
  have hc : 0 ≤ |coef lam i| := abs_nonneg _
  have hA : |coef lam i| * (lam i / 2) ≤ |coef lam i| * lam i := by nlinarith
  exact mul_le_mul hA he (Real.exp_pos _).le (by positivity)

private theorem tsum_norm_kterm0_le {lam : ℕ → ℝ} (h : KernelGood lam) (t : ℝ) :
    ∑' i, ‖kterm lam 0 i t‖ ≤ (∑' i, kb lam 0 i) * Real.exp (-(lam 0 * |t|)) := by
  have hs : Summable (fun i => ‖kterm lam 0 i t‖) := summable_norm_kterm h 0 t
  calc ∑' i, ‖kterm lam 0 i t‖ ≤ ∑' i, kb lam 0 i * Real.exp (-(lam 0 * |t|)) :=
        Summable.tsum_le_tsum (fun i => norm_kterm0_le h i t) hs ((summable_kb h 0).mul_right _)
    _ = (∑' i, kb lam 0 i) * Real.exp (-(lam 0 * |t|)) := tsum_mul_right

private theorem abs_ker_le_exp {lam : ℕ → ℝ} (h : KernelGood lam) (t : ℝ) :
    |ker lam t| ≤ (∑' i, kb lam 0 i) * Real.exp (-(lam 0 * |t|)) := by
  have hs : Summable (fun i => ‖kterm lam 0 i t‖) := summable_norm_kterm h 0 t
  calc |ker lam t| = ‖∑' i, kterm lam 0 i t‖ := by rw [Real.norm_eq_abs]; rfl
    _ ≤ ∑' i, ‖kterm lam 0 i t‖ := norm_tsum_le_tsum_norm hs
    _ ≤ (∑' i, kb lam 0 i) * Real.exp (-(lam 0 * |t|)) := tsum_norm_kterm0_le h t

private theorem tsum_kb_zero_le {lam : ℕ → ℝ} (h : KernelGood lam) : ∑' i, kb lam 0 i ≤ CB * lam 0 + CB / 2 := by
  have hs := summable_kb h 0
  rw [hs.tsum_eq_zero_add]
  have h0 : kb lam 0 0 ≤ CB * lam 0 := by
    unfold kb
    rw [zero_add, pow_one]
    exact mul_le_mul_of_nonneg_right (abs_coef_le_CB h 0) (h.pos 0).le
  have h1 : ∑' k, kb lam 0 (k + 1) ≤ CB / 2 := by
    have hb : ∀ k, kb lam 0 (k + 1) ≤ (CB * (1 / 3 : ℝ)) * (1 / 3 : ℝ) ^ k := by
      intro k
      unfold kb
      have := abs_coef_mul_pow_le_geom h (i := k + 1) (m := 1) (by omega)
      rw [zero_add]
      calc |coef lam (k + 1)| * (lam (k + 1)) ^ 1 ≤ CB * (1 / 3 : ℝ) ^ (k + 1) := this
        _ = (CB * (1 / 3 : ℝ)) * (1 / 3 : ℝ) ^ k := by rw [pow_succ]; ring
    have hg : ∑' k : ℕ, (CB * (1 / 3 : ℝ)) * (1 / 3 : ℝ) ^ k = CB / 2 := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      ring
    rw [← hg]
    exact Summable.tsum_le_tsum hb ((summable_nat_add_iff 1).2 hs)
      ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
  linarith

private theorem abs_ker_le_tail_exp {lam : ℕ → ℝ} (h : KernelGood lam) {r : ℝ} (hr : 0 < r) {t : ℝ} (hrt : r ≤ |t|) :
    |ker lam t| ≤ (CB * (3 / 2) * (2 / r)) * Real.exp (-(lam 0 * |t| / 2)) := by
  have hs : Summable (fun i => ‖kterm lam 0 i t‖) := summable_norm_kterm h 0 t

  have hterm : ∀ i, ‖kterm lam 0 i t‖ ≤ (|coef lam i| * (2 / r)) * Real.exp (-(lam 0 * |t| / 2)) := by
    intro i
    have hl := h.pos i
    have hmono : lam 0 ≤ lam i := h.mono (Nat.zero_le i)

    have hsplit : Real.exp (-(lam i * |t|)) = Real.exp (-(lam i * |t| / 2)) * Real.exp (-(lam i * |t| / 2)) := by
      rw [← Real.exp_add]; congr 1; ring

    have hx : lam i * r / 2 ≤ Real.exp (lam i * r / 2) := by
      have := Real.add_one_le_exp (lam i * r / 2); linarith
    have hfirst : (lam i / 2) * Real.exp (-(lam i * |t| / 2)) ≤ 1 / r := by
      have he : Real.exp (-(lam i * |t| / 2)) ≤ Real.exp (-(lam i * r / 2)) := by
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left hrt hl.le
        linarith
      have hinv : Real.exp (-(lam i * r / 2)) = (Real.exp (lam i * r / 2))⁻¹ := by rw [Real.exp_neg]
      have hepos : 0 < Real.exp (lam i * r / 2) := Real.exp_pos _
      calc (lam i / 2) * Real.exp (-(lam i * |t| / 2)) ≤ (lam i / 2) * Real.exp (-(lam i * r / 2)) :=
            mul_le_mul_of_nonneg_left he (by positivity)
        _ = (lam i / 2) / Real.exp (lam i * r / 2) := by rw [hinv, ← div_eq_mul_inv]
        _ ≤ (lam i / 2) / (lam i * r / 2) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity) hx
        _ = 1 / r := by field_simp
    have hsecond : Real.exp (-(lam i * |t| / 2)) ≤ Real.exp (-(lam 0 * |t| / 2)) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_right hmono (abs_nonneg t)
      linarith
    rw [Real.norm_eq_abs]
    unfold kterm
    simp only [pow_zero, ite_self, mul_one]
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < lam i / 2), abs_of_nonneg (Real.exp_pos _).le, hsplit]
    have hc : 0 ≤ |coef lam i| := abs_nonneg _
    have hr' : (1 : ℝ) / r ≤ 2 / r := by
      rw [div_le_div_iff_of_pos_right hr]; norm_num
    calc |coef lam i| * (lam i / 2) * (Real.exp (-(lam i * |t| / 2)) * Real.exp (-(lam i * |t| / 2)))
        = |coef lam i| * ((lam i / 2) * Real.exp (-(lam i * |t| / 2))) * Real.exp (-(lam i * |t| / 2)) := by ring
      _ ≤ |coef lam i| * (2 / r) * Real.exp (-(lam 0 * |t| / 2)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (hfirst.trans hr') hc) hsecond (Real.exp_pos _).le
          positivity
  have hsum : Summable (fun i => (|coef lam i| * (2 / r)) * Real.exp (-(lam 0 * |t| / 2))) :=
    (((summable_abs_coef h).mul_right _).mul_right _)
  calc |ker lam t| = ‖∑' i, kterm lam 0 i t‖ := by rw [Real.norm_eq_abs]; rfl
    _ ≤ ∑' i, ‖kterm lam 0 i t‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' i, (|coef lam i| * (2 / r)) * Real.exp (-(lam 0 * |t| / 2)) := Summable.tsum_le_tsum hterm hs hsum
    _ = (∑' i, |coef lam i|) * (2 / r) * Real.exp (-(lam 0 * |t| / 2)) := by
        rw [tsum_mul_right, tsum_mul_right]
    _ ≤ (CB * (3 / 2)) * (2 / r) * Real.exp (-(lam 0 * |t| / 2)) := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (tsum_abs_coef_le h) (by positivity))
        exact (Real.exp_pos _).le

end OneVariableFactorization
p2m_reactivate "P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.OneVariableFactorization"

namespace OneVariableFactorization

open Finset Filter Topology

private structure CutoffData (δ : ℝ) (Bs : ℕ → ℝ) (θ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ (⊤ : ℕ∞) θ
  vanish : ∀ j, 1 ≤ j → ∀ t : ℝ, |t| < δ / 2 → iteratedDeriv j θ t = 0
  outer : ∀ j (t : ℝ), δ < |t| → iteratedDeriv j θ t = 0
  bound : ∀ j (t : ℝ), |iteratedDeriv j θ t| ≤ Bs j
  mono : Monotone Bs

private theorem CutoffData.Bs_nonneg {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ} (hc : CutoffData δ Bs θ) (j : ℕ) : 0 ≤ Bs j :=
  (abs_nonneg _).trans (hc.bound j 0)

private theorem natCast_le_top_order (n : ℕ) : ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.mpr le_top

private theorem natCast_lt_top_order (n : ℕ) : ((n : ℕ∞) : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_lt_coe.mpr (ENat.coe_lt_top n)

private theorem contDiffAt_nat_of_top {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (x : ℝ) : ContDiffAt ℝ n f x :=
  (hf.of_le (natCast_le_top_order n)).contDiffAt

private theorem iteratedDeriv_iteratedDeriv' (f : ℝ → ℝ) (m : ℕ) : ∀ k : ℕ, iteratedDeriv k (iteratedDeriv m f) = iteratedDeriv (m + k) f
  | 0 => by rw [iteratedDeriv_zero, Nat.add_zero]
  | k + 1 => by rw [iteratedDeriv_succ, iteratedDeriv_iteratedDeriv' f m k, Nat.add_succ, iteratedDeriv_succ]

private theorem contDiff_iteratedDeriv_of_top {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv m f) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro k _
  rw [iteratedDeriv_iteratedDeriv' f m k]
  exact hf.differentiable_iteratedDeriv (m + k) (natCast_lt_top_order (m + k))

private theorem iteratedDeriv_kerD {lam : ℕ → ℝ} (h : KernelGood lam) (p : ℕ) :
    ∀ k : ℕ, iteratedDeriv k (kerD lam p) = kerD lam (p + k)
  | 0 => by rw [iteratedDeriv_zero, Nat.add_zero]
  | k + 1 => by rw [iteratedDeriv_succ, iteratedDeriv_kerD h p k, deriv_kerD h, Nat.add_assoc]

private theorem contDiff_kerD {lam : ℕ → ℝ} (h : KernelGood lam) (p : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (kerD lam p) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro k _
  rw [iteratedDeriv_kerD h p k]
  exact differentiable_kerD h _

private def rgroup (lam : ℕ → ℝ) (θ : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  iteratedDeriv (2 * n) (θ * kerD lam 0) - θ * kerD lam (2 * n)

private theorem rgroup_apply (lam : ℕ → ℝ) (θ : ℝ → ℝ) (n : ℕ) (t : ℝ) :
    rgroup lam θ n t = iteratedDeriv (2 * n) (θ * ker lam) t - θ t * kerD lam (2 * n) t := rfl

private theorem contDiff_rgroup {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ} (hc : CutoffData δ Bs θ)
    (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (rgroup lam θ n) :=
  (contDiff_iteratedDeriv_of_top (hc.smooth.mul (contDiff_kerD h 0)) _).sub (hc.smooth.mul (contDiff_kerD h _))

private theorem iteratedDeriv_rgroup_apply {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) (n k : ℕ) (t : ℝ) :
    iteratedDeriv k (rgroup lam θ n) t
      = iteratedDeriv (2 * n + k) (θ * kerD lam 0) t - iteratedDeriv k (θ * kerD lam (2 * n)) t := by
  unfold rgroup
  have hf : ContDiffAt ℝ k (iteratedDeriv (2 * n) (θ * kerD lam 0)) t :=
    contDiffAt_nat_of_top (contDiff_iteratedDeriv_of_top (hc.smooth.mul (contDiff_kerD h 0)) _) k t
  have hg : ContDiffAt ℝ k (θ * kerD lam (2 * n)) t := contDiffAt_nat_of_top (hc.smooth.mul (contDiff_kerD h _)) k t
  rw [iteratedDeriv_sub hf hg, iteratedDeriv_iteratedDeriv']

private theorem iteratedDeriv_mul_kerD {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) (p k : ℕ) (t : ℝ) :
    iteratedDeriv k (θ * kerD lam p) t
      = ∑ j ∈ range (k + 1), ((k.choose j : ℕ) : ℝ) * iteratedDeriv j θ t * kerD lam (p + (k - j)) t := by
  rw [iteratedDeriv_mul (contDiffAt_nat_of_top hc.smooth k t) (contDiffAt_nat_of_top (contDiff_kerD h p) k t)]
  apply sum_congr rfl
  intro j _
  rw [iteratedDeriv_kerD h p (k - j)]

private theorem abs_peeled_sum_le {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) (hδ : 0 < δ) (m M : ℕ) (hmM : m ≤ M) (ord : ℕ → ℕ) (hord : ∀ j, ord j ≤ M) (t : ℝ) :
    |∑ j ∈ range m, ((m.choose (j + 1) : ℕ) : ℝ) * iteratedDeriv (j + 1) θ t * kerD lam (ord j) t|
      ≤ (2 : ℝ) ^ m * Bs M * W lam (δ / 2) M := by
  have hr : (0 : ℝ) ≤ δ / 2 := by positivity
  have hBW : 0 ≤ Bs M * W lam (δ / 2) M := mul_nonneg (hc.Bs_nonneg M) (W_nonneg h _ _)

  have hterm : ∀ j ∈ range m, |((m.choose (j + 1) : ℕ) : ℝ) * iteratedDeriv (j + 1) θ t * kerD lam (ord j) t|
      ≤ ((m.choose (j + 1) : ℕ) : ℝ) * (Bs M * W lam (δ / 2) M) := by
    intro j _
    rw [mul_assoc, abs_mul, Nat.abs_cast]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    have h1 := abs_mul_kerD_le h (ord j) hr (hc.vanish (j + 1) (by omega)) (hc.bound (j + 1)) t
    calc |iteratedDeriv (j + 1) θ t * kerD lam (ord j) t| ≤ Bs (j + 1) * W lam (δ / 2) (ord j) := h1
      _ ≤ Bs M * W lam (δ / 2) M :=
          mul_le_mul (hc.mono (by have := mem_range.1 ‹j ∈ range m›; omega)) (W_mono h hr (hord j))
            (W_nonneg h _ _) (hc.Bs_nonneg M)

  have hbin : ∑ j ∈ range m, ((m.choose (j + 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ m := by
    have hN : ∑ j ∈ range m, m.choose (j + 1) ≤ 2 ^ m := by
      have := Nat.sum_range_choose m
      rw [sum_range_succ'] at this
      omega
    exact_mod_cast hN
  calc |∑ j ∈ range m, ((m.choose (j + 1) : ℕ) : ℝ) * iteratedDeriv (j + 1) θ t * kerD lam (ord j) t|
      ≤ ∑ j ∈ range m, |((m.choose (j + 1) : ℕ) : ℝ) * iteratedDeriv (j + 1) θ t * kerD lam (ord j) t| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range m, ((m.choose (j + 1) : ℕ) : ℝ) * (Bs M * W lam (δ / 2) M) := sum_le_sum hterm
    _ = (∑ j ∈ range m, ((m.choose (j + 1) : ℕ) : ℝ)) * (Bs M * W lam (δ / 2) M) := by rw [sum_mul]
    _ ≤ (2 : ℝ) ^ m * (Bs M * W lam (δ / 2) M) := mul_le_mul_of_nonneg_right hbin hBW
    _ = (2 : ℝ) ^ m * Bs M * W lam (δ / 2) M := by ring

private def gb (lam : ℕ → ℝ) (δ : ℝ) (Bs : ℕ → ℝ) (n k : ℕ) : ℝ :=
  2 * (2 : ℝ) ^ (2 * n + k) * Bs (2 * n + k) * W lam (δ / 2) (2 * n + k)

private theorem gb_nonneg {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ} (hc : CutoffData δ Bs θ)
    (n k : ℕ) : 0 ≤ gb lam δ Bs n k := by
  unfold gb
  have := hc.Bs_nonneg (2 * n + k)
  have := W_nonneg h (δ / 2) (2 * n + k)
  positivity

private theorem abs_iteratedDeriv_rgroup_le {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) (hδ : 0 < δ) (n k : ℕ) (t : ℝ) :
    |iteratedDeriv k (rgroup lam θ n) t| ≤ gb lam δ Bs n k := by
  rw [iteratedDeriv_rgroup_apply h hc, iteratedDeriv_mul_kerD h hc, iteratedDeriv_mul_kerD h hc]

  rw [sum_range_succ', sum_range_succ']
  have h00 : ((2 * n + k).choose 0 : ℕ) = 1 := Nat.choose_zero_right _
  have hk0 : (k.choose 0 : ℕ) = 1 := Nat.choose_zero_right _
  simp only [h00, hk0, Nat.cast_one, one_mul, Nat.sub_zero, Nat.zero_add]

  set c := iteratedDeriv 0 θ t * kerD lam (2 * n + k) t with hc0
  have hS1 := abs_peeled_sum_le h hc hδ (2 * n + k) (2 * n + k) le_rfl (fun j => 0 + (2 * n + k - (j + 1)))
    (fun j => by show 0 + (2 * n + k - (j + 1)) ≤ 2 * n + k; omega) t
  have hS2 := abs_peeled_sum_le h hc hδ k (2 * n + k) (by omega) (fun j => 2 * n + (k - (j + 1)))
    (fun j => by show 2 * n + (k - (j + 1)) ≤ 2 * n + k; omega) t
  simp only [Nat.zero_add] at hS1
  have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (2 * n + k) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hBW : 0 ≤ Bs (2 * n + k) * W lam (δ / 2) (2 * n + k) := mul_nonneg (hc.Bs_nonneg _) (W_nonneg h _ _)
  unfold gb
  calc |(∑ j ∈ range (2 * n + k), ((2 * n + k).choose (j + 1) : ℝ) * iteratedDeriv (j + 1) θ t
            * kerD lam (2 * n + k - (j + 1)) t + c)
          - (∑ j ∈ range k, (k.choose (j + 1) : ℝ) * iteratedDeriv (j + 1) θ t * kerD lam (2 * n + (k - (j + 1))) t + c)|
      = |(∑ j ∈ range (2 * n + k), ((2 * n + k).choose (j + 1) : ℝ) * iteratedDeriv (j + 1) θ t
            * kerD lam (2 * n + k - (j + 1)) t)
          - (∑ j ∈ range k, (k.choose (j + 1) : ℝ) * iteratedDeriv (j + 1) θ t * kerD lam (2 * n + (k - (j + 1))) t)| := by
        congr 1; ring
    _ ≤ |∑ j ∈ range (2 * n + k), ((2 * n + k).choose (j + 1) : ℝ) * iteratedDeriv (j + 1) θ t
            * kerD lam (2 * n + k - (j + 1)) t|
        + |∑ j ∈ range k, (k.choose (j + 1) : ℝ) * iteratedDeriv (j + 1) θ t * kerD lam (2 * n + (k - (j + 1))) t| :=
        abs_sub _ _
    _ ≤ (2 : ℝ) ^ (2 * n + k) * Bs (2 * n + k) * W lam (δ / 2) (2 * n + k)
        + (2 : ℝ) ^ k * Bs (2 * n + k) * W lam (δ / 2) (2 * n + k) := add_le_add hS1 hS2
    _ ≤ (2 : ℝ) ^ (2 * n + k) * Bs (2 * n + k) * W lam (δ / 2) (2 * n + k)
        + (2 : ℝ) ^ (2 * n + k) * Bs (2 * n + k) * W lam (δ / 2) (2 * n + k) := by
        apply add_le_add le_rfl
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right hpow hBW
    _ = 2 * (2 : ℝ) ^ (2 * n + k) * Bs (2 * n + k) * W lam (δ / 2) (2 * n + k) := by ring

private def mast (lam : ℕ → ℝ) (δ : ℝ) (Bs : ℕ → ℝ) (k n : ℕ) : ℝ :=
  ebar (uOf lam) n * (8 : ℝ) ^ n * Bs (2 * n + k) * W lam (δ / 2) (2 * n + k)

private theorem uOf_le_sixteenth {lam : ℕ → ℝ} (h : KernelGood lam) (n : ℕ) : uOf lam n ≤ 1 / 16 :=
  (h.uOf_le_zero n).trans h.uOf_zero_le

private theorem mast_nonneg {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ} (hc : CutoffData δ Bs θ)
    (k n : ℕ) : 0 ≤ mast lam δ Bs k n := by
  unfold mast
  have := ebar_nonneg h.uOf_nonneg n
  have := hc.Bs_nonneg (2 * n + k)
  have := W_nonneg h (δ / 2) (2 * n + k)
  positivity

private theorem head_term_le {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ} (hc : CutoffData δ Bs θ)
    (hm : MasterGood δ Bs lam) {k n i : ℕ} (hni : n ≤ i + 1) (hki : k < i) :
    Bs (2 * n + k) * wterm lam (δ / 2) (2 * n + k) i ≤ (1 / 2 : ℝ) ^ i := by
  have hk5 := hm.k5 i
  have hl1 := h.one_le i
  have hlpos := h.pos i
  have he : 0 ≤ Real.exp (-(lam i * δ / 2)) := (Real.exp_pos _).le
  have hcoef := abs_coef_le_CB h i
  have hCB := CB_pos

  have hw : wterm lam (δ / 2) (2 * n + k) i
      = |coef lam i| * (lam i) ^ (2 * n + k + 1) * Real.exp (-(lam i * δ / 2)) := by
    unfold wterm; rw [mul_div_assoc]
  rw [hw]
  have hpow : (lam i) ^ (2 * n + k + 1) ≤ (lam i) ^ (3 * i + 3) := pow_le_pow_right₀ hl1 (by omega)
  have hBs : Bs (2 * n + k) ≤ Bs (3 * i + 3) := hc.mono (by omega)
  have hBs0 := hc.Bs_nonneg (2 * n + k)
  have hB3 := hc.Bs_nonneg (3 * i + 3)

  calc Bs (2 * n + k) * (|coef lam i| * (lam i) ^ (2 * n + k + 1) * Real.exp (-(lam i * δ / 2)))
      ≤ Bs (3 * i + 3) * (CB * (lam i) ^ (3 * i + 3) * Real.exp (-(lam i * δ / 2))) := by
        apply mul_le_mul hBs _ (by positivity) hB3
        apply mul_le_mul_of_nonneg_right _ he
        exact mul_le_mul hcoef hpow (by positivity) hCB.le
    _ = CB * Bs (3 * i + 3) * (lam i) ^ (3 * i + 3) * Real.exp (-(lam i * δ / 2)) := by ring
    _ ≤ (1 / 2 : ℝ) ^ i := hk5

private theorem tail_term_le {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} (hδ : 0 < δ) {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) (hm : MasterGood δ Bs lam) {k n i : ℕ} (hin : i + 2 ≤ n) (hkn : k + 1 ≤ n) :
    ebar (uOf lam) n * (8 : ℝ) ^ n * Bs (2 * n + k) * wterm lam (δ / 2) (2 * n + k) i
      ≤ (1 / 2 : ℝ) ^ n * |coef lam i| := by
  have htb := hm.tail_bound (n := n) (by omega)
  have hl1 := h.one_le i
  have hlpos := h.pos i
  have hmono : lam i ≤ lam (n - 2) := h.mono (by omega)
  have hl2 := h.pos (n - 2)
  have hebar := ebar_nonneg h.uOf_nonneg n
  have hBs0 := hc.Bs_nonneg (2 * n + k)
  have hB3 := hc.Bs_nonneg (3 * n)
  have hBs : Bs (2 * n + k) ≤ Bs (3 * n) := hc.mono (by omega)
  have he1 : Real.exp (-(lam i * (δ / 2))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ lam i * (δ / 2) := by positivity
    linarith
  have he0 : 0 ≤ Real.exp (-(lam i * (δ / 2))) := (Real.exp_pos _).le
  have hpow : (lam i) ^ (2 * n + k + 1) ≤ (lam (n - 2)) ^ (3 * n) :=
    (pow_le_pow_left₀ hlpos.le hmono _).trans (pow_le_pow_right₀ (h.one_le (n - 2)) (by omega))
  have hcoef := abs_nonneg (coef lam i)
  have hpos8 : (0 : ℝ) ≤ ebar (uOf lam) n * 8 ^ n := by positivity
  have hlp : (0 : ℝ) ≤ (lam i) ^ (2 * n + k + 1) := by positivity
  unfold wterm

  calc ebar (uOf lam) n * (8 : ℝ) ^ n * Bs (2 * n + k)
          * (|coef lam i| * (lam i) ^ (2 * n + k + 1) * Real.exp (-(lam i * (δ / 2))))
      = (ebar (uOf lam) n * (8 : ℝ) ^ n * Bs (2 * n + k) * (lam i) ^ (2 * n + k + 1))
          * |coef lam i| * Real.exp (-(lam i * (δ / 2))) := by ring
    _ ≤ (ebar (uOf lam) n * (8 : ℝ) ^ n * Bs (3 * n) * (lam (n - 2)) ^ (3 * n)) * |coef lam i| * 1 := by
        apply mul_le_mul _ he1 he0 (by positivity)
        apply mul_le_mul_of_nonneg_right _ hcoef
        exact mul_le_mul (mul_le_mul_of_nonneg_left hBs hpos8) hpow hlp (by positivity)
    _ ≤ (1 / 2 : ℝ) ^ n * |coef lam i| * 1 := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htb hcoef) zero_le_one
    _ = (1 / 2 : ℝ) ^ n * |coef lam i| := mul_one _

private theorem summable_mast {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} (hδ : 0 < δ) {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) (hm : MasterGood δ Bs lam) (k : ℕ) : Summable (mast lam δ Bs k) := by
  have hr : (0 : ℝ) ≤ δ / 2 := by positivity

  rw [← summable_nat_add_iff (k + 2)]
  have hdom : Summable (fun n : ℕ => 2 * (2 / 3 : ℝ) ^ (n + (k + 2)) + CB * (3 / 2) * (1 / 2 : ℝ) ^ (n + (k + 2))) := by
    apply Summable.add
    · have := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num)).mul_left
        (2 * (2 / 3 : ℝ) ^ (k + 2))
      refine this.congr (fun n => ?_)
      rw [pow_add]; ring
    · have := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left
        (CB * (3 / 2) * (1 / 2 : ℝ) ^ (k + 2))
      refine this.congr (fun n => ?_)
      rw [pow_add]; ring
  refine Summable.of_nonneg_of_le (fun n => mast_nonneg h hc k _) (fun n => ?_) hdom

  set N := n + (k + 2) with hN
  have hNk : k + 1 ≤ N := by omega
  have hN2 : 2 ≤ N := by omega
  have hsw := summable_wterm h hr (2 * N + k)
  have hsplit := hsw.sum_add_tsum_nat_add (N - 1)
  have hebar8 : ebar (uOf lam) N * (8 : ℝ) ^ N ≤ (2 / 3 : ℝ) ^ N :=
    ebar_mul_eight_pow_le h.uOf_nonneg (uOf_le_sixteenth h) N
  have hebar8_nonneg : (0 : ℝ) ≤ ebar (uOf lam) N * 8 ^ N := by
    have := ebar_nonneg h.uOf_nonneg N; positivity
  have hBs0 := hc.Bs_nonneg (2 * N + k)

  have hmast : mast lam δ Bs k N
      = (ebar (uOf lam) N * (8 : ℝ) ^ N * Bs (2 * N + k)) * (∑ i ∈ range (N - 1), wterm lam (δ / 2) (2 * N + k) i)
        + (ebar (uOf lam) N * (8 : ℝ) ^ N) * ∑' i, (Bs (2 * N + k) * wterm lam (δ / 2) (2 * N + k) (i + (N - 1))) := by
    unfold mast W
    rw [← hsplit, tsum_mul_left]
    ring

  have hfin : (ebar (uOf lam) N * (8 : ℝ) ^ N * Bs (2 * N + k)) * (∑ i ∈ range (N - 1), wterm lam (δ / 2) (2 * N + k) i)
      ≤ CB * (3 / 2) * (1 / 2 : ℝ) ^ N := by
    rw [mul_sum]
    have h1 : ∀ i ∈ range (N - 1),
        ebar (uOf lam) N * (8 : ℝ) ^ N * Bs (2 * N + k) * wterm lam (δ / 2) (2 * N + k) i
          ≤ (1 / 2 : ℝ) ^ N * |coef lam i| := by
      intro i hi
      exact tail_term_le h hδ hc hm (by have := mem_range.1 hi; omega) hNk
    calc ∑ i ∈ range (N - 1), ebar (uOf lam) N * (8 : ℝ) ^ N * Bs (2 * N + k) * wterm lam (δ / 2) (2 * N + k) i
        ≤ ∑ i ∈ range (N - 1), (1 / 2 : ℝ) ^ N * |coef lam i| := sum_le_sum h1
      _ = (1 / 2 : ℝ) ^ N * ∑ i ∈ range (N - 1), |coef lam i| := by rw [mul_sum]
      _ ≤ (1 / 2 : ℝ) ^ N * (CB * (3 / 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact ((summable_abs_coef h).sum_le_tsum _ (fun i _ => abs_nonneg _)).trans (tsum_abs_coef_le h)
      _ = CB * (3 / 2) * (1 / 2 : ℝ) ^ N := by ring

  have htail : ∑' i, (Bs (2 * N + k) * wterm lam (δ / 2) (2 * N + k) (i + (N - 1))) ≤ 2 := by
    have hg : Summable (fun i : ℕ => (1 / 2 : ℝ) ^ (i + (N - 1))) :=
      (summable_nat_add_iff (N - 1)).2 (summable_geometric_of_lt_one (by norm_num) (by norm_num))
    have hsum : ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + (N - 1)) ≤ 2 := by
      have hfull : ∑' i : ℕ, (1 / 2 : ℝ) ^ i = 2 := by
        rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
      have hle : ∑' i : ℕ, (1 / 2 : ℝ) ^ (i + (N - 1)) ≤ ∑' i : ℕ, (1 / 2 : ℝ) ^ i := by
        refine Summable.tsum_le_tsum (fun i => ?_) hg (summable_geometric_of_lt_one (by norm_num) (by norm_num))
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith
    have hsB : Summable (fun i => Bs (2 * N + k) * wterm lam (δ / 2) (2 * N + k) (i + (N - 1))) :=
      ((summable_nat_add_iff (N - 1)).2 hsw).mul_left _
    refine le_trans (Summable.tsum_le_tsum (fun i => ?_) hsB hg) hsum
    exact head_term_le h hc hm (by omega) (by omega)
  calc mast lam δ Bs k N
      ≤ CB * (3 / 2) * (1 / 2 : ℝ) ^ N + (ebar (uOf lam) N * (8 : ℝ) ^ N) * 2 := by
        rw [hmast]
        exact add_le_add hfin (mul_le_mul_of_nonneg_left htail hebar8_nonneg)
    _ ≤ CB * (3 / 2) * (1 / 2 : ℝ) ^ N + (2 / 3 : ℝ) ^ N * 2 := by
        apply add_le_add le_rfl
        exact mul_le_mul_of_nonneg_right hebar8 (by norm_num)
    _ = 2 * (2 / 3 : ℝ) ^ (n + (k + 2)) + CB * (3 / 2) * (1 / 2 : ℝ) ^ (n + (k + 2)) := by
        rw [hN]; ring

private theorem summable_ebar_mul_gb {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} (hδ : 0 < δ) {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) (hm : MasterGood δ Bs lam) (k : ℕ) :
    Summable (fun n => ebar (uOf lam) n * gb lam δ Bs n k) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (ebar_nonneg h.uOf_nonneg n) (gb_nonneg h hc n k))
    (fun n => ?_) ((summable_mast h hδ hc hm k).mul_left (2 * (2 : ℝ) ^ k))
  unfold gb mast
  have hebar := ebar_nonneg h.uOf_nonneg n
  have hBs := hc.Bs_nonneg (2 * n + k)
  have hW := W_nonneg h (δ / 2) (2 * n + k)

  have h4 : (2 : ℝ) ^ (2 * n + k) = (4 : ℝ) ^ n * 2 ^ k := by
    rw [pow_add, pow_mul]; norm_num
  have h48 : (4 : ℝ) ^ n ≤ (8 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  rw [h4]
  have hX : 0 ≤ ebar (uOf lam) n * (2 * 2 ^ k) * Bs (2 * n + k) * W lam (δ / 2) (2 * n + k) := by positivity
  calc ebar (uOf lam) n * (2 * ((4 : ℝ) ^ n * 2 ^ k) * Bs (2 * n + k) * W lam (δ / 2) (2 * n + k))
      = (ebar (uOf lam) n * (2 * 2 ^ k) * Bs (2 * n + k) * W lam (δ / 2) (2 * n + k)) * (4 : ℝ) ^ n := by ring
    _ ≤ (ebar (uOf lam) n * (2 * 2 ^ k) * Bs (2 * n + k) * W lam (δ / 2) (2 * n + k)) * (8 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left h48 hX
    _ = 2 * (2 : ℝ) ^ k * (ebar (uOf lam) n * 8 ^ n * Bs (2 * n + k) * W lam (δ / 2) (2 * n + k)) := by ring

end OneVariableFactorization
p2m_reactivate "P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.OneVariableFactorization"

namespace OneVariableFactorization

open Finset Filter Topology

private def psiN (lam : ℕ → ℝ) (θ : ℝ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ range (N + 1), ((-1 : ℝ) ^ n * es (uOf lam) N n) * rgroup lam θ n t

private def psiTerm (lam : ℕ → ℝ) (θ : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  fun t => ((-1 : ℝ) ^ n * eLim (uOf lam) n) * rgroup lam θ n t

private def psi (lam : ℕ → ℝ) (θ : ℝ → ℝ) (t : ℝ) : ℝ := ∑' n, psiTerm lam θ n t

private theorem psiN_eq (lam : ℕ → ℝ) (θ : ℝ → ℝ) (N : ℕ) (t : ℝ) :
    psiN lam θ N t
      = (∑ n ∈ range (N + 1), ((-1 : ℝ) ^ n * es (uOf lam) N n) * iteratedDeriv (2 * n) (θ * ker lam) t)
        - θ t * ∑ n ∈ range (N + 1), ((-1 : ℝ) ^ n * es (uOf lam) N n) * kerD lam (2 * n) t := by
  unfold psiN
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n _
  rw [rgroup_apply]
  ring

private theorem ker_shiftN_recursion {lam : ℕ → ℝ} (h : KernelGood lam) (N : ℕ) :
    ker (shiftN (N + 1) lam)
      = fun t => ker (shiftN N lam) t - uOf lam N * deriv (deriv (ker (shiftN N lam))) t := by
  have hμ : KernelGood (shiftN N lam) := h.shiftN N
  rw [deriv_deriv_ker hμ, ← uOf_shiftN_zero lam N, shiftN_succ]
  exact (ker_step hμ).symm

private theorem iteratedDeriv_two_mul_ker {lam : ℕ → ℝ} (h : KernelGood lam) (n : ℕ) :
    iteratedDeriv (2 * n) (ker lam) = kerD lam (2 * n) :=
  iteratedDeriv_ker h (2 * n)

private theorem abs_rgroup_le {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ} (hc : CutoffData δ Bs θ)
    (hδ : 0 < δ) (n : ℕ) (t : ℝ) : |rgroup lam θ n t| ≤ gb lam δ Bs n 0 := by
  have := abs_iteratedDeriv_rgroup_le h hc hδ n 0 t
  rwa [iteratedDeriv_zero] at this

private theorem rgroup_eq_zero_of_outer {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) (n : ℕ) {t : ℝ} (ht : δ < |t|) : rgroup lam θ n t = 0 := by
  have hθ : θ t = 0 := by
    have := hc.outer 0 t ht
    rwa [iteratedDeriv_zero] at this
  unfold rgroup
  show iteratedDeriv (2 * n) (θ * kerD lam 0) t - θ t * kerD lam (2 * n) t = 0
  rw [iteratedDeriv_mul_kerD h hc, hθ, zero_mul, sub_zero]
  apply sum_eq_zero
  intro j _
  rw [hc.outer j t ht, mul_zero, zero_mul]

private theorem psiN_eq_zero_of_outer {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) (N : ℕ) {t : ℝ} (ht : δ < |t|) : psiN lam θ N t = 0 := by
  unfold psiN
  apply sum_eq_zero
  intro n _
  rw [rgroup_eq_zero_of_outer h hc n ht, mul_zero]

private theorem psi_eq_zero_of_outer {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) {t : ℝ} (ht : δ < |t|) : psi lam θ t = 0 := by
  unfold psi psiTerm
  simp_rw [rgroup_eq_zero_of_outer h hc _ ht, mul_zero, tsum_zero]

private theorem tsupport_subset_Icc_of_outer {E : Type*} [Zero E] {δ : ℝ} {f : ℝ → E} (hf : ∀ t : ℝ, δ < |t| → f t = 0) :
    tsupport f ⊆ Set.Icc (-δ) δ := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hnot
  apply ht
  apply hf
  rw [Set.mem_Icc] at hnot
  rcases lt_or_ge δ |t| with hlt | hle
  · exact hlt
  · exact absurd (abs_le.1 hle) hnot

private theorem tsupport_psi_subset {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) : tsupport (psi lam θ) ⊆ Set.Icc (-δ) δ :=
  tsupport_subset_Icc_of_outer (fun _ ht => psi_eq_zero_of_outer h hc ht)

private theorem tsupport_psiN_subset {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) (N : ℕ) : tsupport (psiN lam θ N) ⊆ Set.Icc (-δ) δ :=
  tsupport_subset_Icc_of_outer (fun _ ht => psiN_eq_zero_of_outer h hc N ht)

private theorem eLim_uOf_nonneg {lam : ℕ → ℝ} (h : KernelGood lam) (n : ℕ) : 0 ≤ eLim (uOf lam) n :=
  eLim_nonneg h.uOf_nonneg h.uOf_succ_le n

private theorem eLim_uOf_le_ebar {lam : ℕ → ℝ} (h : KernelGood lam) (n : ℕ) : eLim (uOf lam) n ≤ ebar (uOf lam) n :=
  eLim_le_ebar h.uOf_nonneg h.uOf_succ_le n

private theorem contDiff_psiTerm {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ} (hc : CutoffData δ Bs θ)
    (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (psiTerm lam θ n) :=
  contDiff_const.mul (contDiff_rgroup h hc n)

private theorem norm_iteratedFDeriv_psiTerm_le {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) (hδ : 0 < δ) (k n : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ k (psiTerm lam θ n) t‖ ≤ ebar (uOf lam) n * gb lam δ Bs n k := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
  unfold psiTerm
  rw [iteratedDeriv_const_mul_field, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (eLim_uOf_nonneg h n)]
  exact mul_le_mul (eLim_uOf_le_ebar h n) (abs_iteratedDeriv_rgroup_le h hc hδ n k t) (abs_nonneg _)
    (ebar_nonneg h.uOf_nonneg n)

private theorem contDiff_psi {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} (hδ : 0 < δ) {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) (hm : MasterGood δ Bs lam) : ContDiff ℝ (⊤ : ℕ∞) (psi lam θ) := by
  unfold psi
  exact contDiff_tsum (fun n => contDiff_psiTerm h hc n) (fun k _ => summable_ebar_mul_gb h hδ hc hm k)
    (fun k n t _ => norm_iteratedFDeriv_psiTerm_le h hc hδ k n t)

private def mast0 (lam : ℕ → ℝ) (δ : ℝ) (Bs : ℕ → ℝ) : ℝ := ∑' n, ebar (uOf lam) n * gb lam δ Bs n 0

private theorem abs_psiN_term_le {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ} (hc : CutoffData δ Bs θ)
    (hδ : 0 < δ) (N n : ℕ) (t : ℝ) :
    |((-1 : ℝ) ^ n * es (uOf lam) N n) * rgroup lam θ n t| ≤ ebar (uOf lam) n * gb lam δ Bs n 0 := by
  rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (es_nonneg h.uOf_nonneg N n)]
  exact mul_le_mul (es_le_ebar h.uOf_nonneg h.uOf_succ_le N n) (abs_rgroup_le h hc hδ n t) (abs_nonneg _)
    (ebar_nonneg h.uOf_nonneg n)

private theorem abs_psiN_le {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} (hδ : 0 < δ) {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) (hm : MasterGood δ Bs lam) (N : ℕ) (t : ℝ) : |psiN lam θ N t| ≤ mast0 lam δ Bs := by
  unfold psiN mast0
  have hs := summable_ebar_mul_gb h hδ hc hm 0
  calc |∑ n ∈ range (N + 1), ((-1 : ℝ) ^ n * es (uOf lam) N n) * rgroup lam θ n t|
      ≤ ∑ n ∈ range (N + 1), |((-1 : ℝ) ^ n * es (uOf lam) N n) * rgroup lam θ n t| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ range (N + 1), ebar (uOf lam) n * gb lam δ Bs n 0 := sum_le_sum (fun n _ => abs_psiN_term_le h hc hδ N n t)
    _ ≤ ∑' n, ebar (uOf lam) n * gb lam δ Bs n 0 :=
        hs.sum_le_tsum _ (fun n _ => mul_nonneg (ebar_nonneg h.uOf_nonneg n) (gb_nonneg h hc n 0))

private theorem abs_psiTerm_le {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ} (hc : CutoffData δ Bs θ)
    (hδ : 0 < δ) (n : ℕ) (t : ℝ) : |psiTerm lam θ n t| ≤ ebar (uOf lam) n * gb lam δ Bs n 0 := by
  have := norm_iteratedFDeriv_psiTerm_le h hc hδ 0 n t
  rwa [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_zero, Real.norm_eq_abs] at this

private theorem summable_psiTerm {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} (hδ : 0 < δ) {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) (hm : MasterGood δ Bs lam) (t : ℝ) : Summable (fun n => psiTerm lam θ n t) :=
  Summable.of_norm_bounded (summable_ebar_mul_gb h hδ hc hm 0)
    (fun n => by rw [Real.norm_eq_abs]; exact abs_psiTerm_le h hc hδ n t)

private theorem abs_psi_le {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} (hδ : 0 < δ) {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) (hm : MasterGood δ Bs lam) (t : ℝ) : |psi lam θ t| ≤ mast0 lam δ Bs := by
  unfold psi mast0
  have hs : Summable (fun n => ‖psiTerm lam θ n t‖) := by
    simpa only [Real.norm_eq_abs] using (summable_psiTerm h hδ hc hm t).abs
  calc |∑' n, psiTerm lam θ n t| = ‖∑' n, psiTerm lam θ n t‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n, ‖psiTerm lam θ n t‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, ebar (uOf lam) n * gb lam δ Bs n 0 :=
        Summable.tsum_le_tsum (fun n => by rw [Real.norm_eq_abs]; exact abs_psiTerm_le h hc hδ n t) hs
          (summable_ebar_mul_gb h hδ hc hm 0)

private theorem psiN_eq_tsum (lam : ℕ → ℝ) (θ : ℝ → ℝ) (N : ℕ) (t : ℝ) :
    psiN lam θ N t = ∑' n, (if n ≤ N then ((-1 : ℝ) ^ n * es (uOf lam) N n) * rgroup lam θ n t else 0) := by
  unfold psiN
  rw [tsum_eq_sum (s := range (N + 1))]
  · apply sum_congr rfl
    intro n hn
    rw [if_pos (by have := mem_range.1 hn; omega)]
  · intro n hn
    rw [if_neg (fun hle => hn (mem_range.2 (by omega)))]

private theorem tendsto_psiN {lam : ℕ → ℝ} (h : KernelGood lam) {δ : ℝ} (hδ : 0 < δ) {Bs : ℕ → ℝ} {θ : ℝ → ℝ}
    (hc : CutoffData δ Bs θ) (hm : MasterGood δ Bs lam) (t : ℝ) :
    Tendsto (fun N => psiN lam θ N t) atTop (𝓝 (psi lam θ t)) := by
  simp_rw [psiN_eq_tsum]
  unfold psi
  apply tendsto_tsum_of_dominated_convergence (summable_ebar_mul_gb h hδ hc hm 0)
  · intro n

    have h1 : Tendsto (fun N => ((-1 : ℝ) ^ n * es (uOf lam) N n) * rgroup lam θ n t) atTop
        (𝓝 (((-1 : ℝ) ^ n * eLim (uOf lam) n) * rgroup lam θ n t)) :=
      ((tendsto_es h.uOf_nonneg h.uOf_succ_le n).const_mul _).mul_const _
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop n] with N hN
    rw [if_pos hN]
  · refine Eventually.of_forall (fun N n => ?_)
    split_ifs
    · rw [Real.norm_eq_abs]; exact abs_psiN_term_le h hc hδ N n t
    · rw [norm_zero]; exact mul_nonneg (ebar_nonneg h.uOf_nonneg n) (gb_nonneg h hc n 0)

end OneVariableFactorization
p2m_reactivate "P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.OneVariableFactorization"

namespace OneVariableFactorization

open Finset Filter Topology MeasureTheory

private theorem integrable_exp_neg_mul_abs {b : ℝ} (hb : 0 < b) : Integrable (fun t : ℝ => Real.exp (-(b * |t|))) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  apply IntegrableOn.union
  · refine (integrableOn_exp_mul_Iic hb 0).congr_fun (fun t ht => ?_) measurableSet_Iic
    have ht' : t ≤ 0 := Set.mem_Iic.1 ht
    rw [abs_of_nonpos ht']; ring_nf
  · refine (integrableOn_exp_mul_Ioi (neg_neg_of_pos hb) 0).congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht' : 0 < t := Set.mem_Ioi.1 ht
    beta_reduce
    rw [abs_of_pos ht', neg_mul]

private theorem integral_exp_neg_mul_abs {b : ℝ} (hb : 0 < b) : ∫ t : ℝ, Real.exp (-(b * |t|)) = 2 / b := by
  rw [integral_comp_abs (f := fun x => Real.exp (-(b * x)))]
  have h := integral_exp_mul_Ioi (neg_neg_of_pos hb) 0
  simp only [mul_zero, Real.exp_zero] at h
  have h' : ∫ x : ℝ in Set.Ioi 0, Real.exp (-(b * x)) = 1 / b := by
    rw [show (fun x : ℝ => Real.exp (-(b * x))) = fun x : ℝ => Real.exp (-b * x) from funext (fun x => by rw [neg_mul])]
    rw [h]; field_simp
  rw [h']; ring

private theorem integral_exp_neg_mul_abs_half {b : ℝ} (hb : 0 < b) : ∫ t : ℝ, Real.exp (-(b * |t| / 2)) = 4 / b := by
  have hb2 : 0 < b / 2 := by positivity
  have := integral_exp_neg_mul_abs hb2
  rw [show (fun t : ℝ => Real.exp (-(b * |t| / 2))) = fun t : ℝ => Real.exp (-(b / 2 * |t|)) from
    funext (fun t => by ring_nf)]
  rw [this]; ring

private theorem integrable_exp_neg_mul_abs_half {b : ℝ} (hb : 0 < b) : Integrable (fun t : ℝ => Real.exp (-(b * |t| / 2))) := by
  have hb2 : 0 < b / 2 := by positivity
  have := integrable_exp_neg_mul_abs hb2
  rwa [show (fun t : ℝ => Real.exp (-(b * |t| / 2))) = fun t : ℝ => Real.exp (-(b / 2 * |t|)) from
    funext (fun t => by ring_nf)]

private theorem kterm0_eq (lam : ℕ → ℝ) (i : ℕ) :
    kterm lam 0 i = fun t => (coef lam i * (lam i / 2)) * Real.exp (-(lam i * |t|)) := by
  funext t
  unfold kterm
  simp only [pow_zero, ite_self, mul_one]

private theorem continuous_kterm0 (lam : ℕ → ℝ) (i : ℕ) : Continuous (kterm lam 0 i) := by
  rw [kterm0_eq]
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_abs).neg)

private theorem integrable_kterm0 {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) : Integrable (kterm lam 0 i) := by
  rw [kterm0_eq]
  exact (integrable_exp_neg_mul_abs (h.pos i)).const_mul _

private theorem integral_kterm0 {lam : ℕ → ℝ} (h : KernelGood lam) (i : ℕ) : ∫ t, kterm lam 0 i t = coef lam i := by
  rw [kterm0_eq]
  simp only
  rw [integral_const_mul, integral_exp_neg_mul_abs (h.pos i)]
  have := h.ne_zero i
  field_simp

private theorem integrable_ker_dominant {lam : ℕ → ℝ} (h : KernelGood lam) :
    Integrable (fun t : ℝ => (∑' i, kb lam 0 i) * Real.exp (-(lam 0 * |t|))) :=
  (integrable_exp_neg_mul_abs (h.pos 0)).const_mul _

private theorem integrable_ker {lam : ℕ → ℝ} (h : KernelGood lam) : Integrable (ker lam) := by
  refine (integrable_ker_dominant h).mono' (continuous_kerD h 0).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs]
  exact abs_ker_le_exp h t

private theorem norm_sum_kterm0_le {lam : ℕ → ℝ} (h : KernelGood lam) (M : ℕ) (t : ℝ) :
    ‖∑ i ∈ range M, kterm lam 0 i t‖ ≤ (∑' i, kb lam 0 i) * Real.exp (-(lam 0 * |t|)) := by
  have hs : Summable (fun i => ‖kterm lam 0 i t‖) := summable_norm_kterm h 0 t
  calc ‖∑ i ∈ range M, kterm lam 0 i t‖ ≤ ∑ i ∈ range M, ‖kterm lam 0 i t‖ := norm_sum_le _ _
    _ ≤ ∑' i, ‖kterm lam 0 i t‖ := hs.sum_le_tsum _ (fun i _ => norm_nonneg _)
    _ ≤ (∑' i, kb lam 0 i) * Real.exp (-(lam 0 * |t|)) := tsum_norm_kterm0_le h t

private theorem integral_ker {lam : ℕ → ℝ} (h : KernelGood lam) : ∫ t, ker lam t = 1 := by

  have h1 : Tendsto (fun M => ∫ t, ∑ i ∈ range M, kterm lam 0 i t) atTop (𝓝 (∫ t, ker lam t)) := by
    refine tendsto_integral_of_dominated_convergence _ (fun M => ?_) (integrable_ker_dominant h)
      (fun M => Eventually.of_forall (fun t => norm_sum_kterm0_le h M t)) (Eventually.of_forall (fun t => ?_))
    · exact (continuous_finsetSum _ (fun i _ => continuous_kterm0 lam i)).aestronglyMeasurable
    · exact (summable_kterm h 0 t).hasSum.tendsto_sum_nat

  have h2 : ∀ M, ∫ t, ∑ i ∈ range M, kterm lam 0 i t = ∑ i ∈ range M, coef lam i := by
    intro M
    rw [integral_finsetSum _ (fun i _ => integrable_kterm0 h i)]
    exact sum_congr rfl (fun i _ => integral_kterm0 h i)
  have h3 : Tendsto (fun M => ∑ i ∈ range M, coef lam i) atTop (𝓝 (1 : ℝ)) := by
    have := (summable_coef h).hasSum.tendsto_sum_nat
    rwa [tsum_coef_eq_one h] at this
  simp_rw [h2] at h1
  exact tendsto_nhds_unique h1 h3

private theorem tsum_kb_mul_integral_le {lam : ℕ → ℝ} (h : KernelGood lam) :
    (∑' i, kb lam 0 i) * (2 / lam 0) ≤ 2 * CB + CB / 4 := by
  have hK := tsum_kb_zero_le h
  have hl4 := h.four_le_all 0
  have hlpos := h.pos 0
  have hCB := CB_pos
  have hKnn : 0 ≤ ∑' i, kb lam 0 i := tsum_nonneg (kb_nonneg h 0)
  calc (∑' i, kb lam 0 i) * (2 / lam 0) ≤ (CB * lam 0 + CB / 2) * (2 / lam 0) :=
        mul_le_mul_of_nonneg_right hK (by positivity)
    _ = 2 * CB + CB / lam 0 := by field_simp
    _ ≤ 2 * CB + CB / 4 := by
        apply add_le_add le_rfl
        exact div_le_div_of_nonneg_left hCB.le (by norm_num) hl4

private theorem nat_le_lam {lam : ℕ → ℝ} (h : KernelGood lam) (N : ℕ) : (N : ℝ) ≤ lam N := by
  have h1 := h.mul_two_pow_le 0 N
  rw [Nat.zero_add] at h1
  have h4 := h.four_le_all 0
  have h2 : ((N : ℝ)) ≤ (2 : ℝ) ^ N := by exact_mod_cast Nat.lt_two_pow_self.le
  have h3 : (0 : ℝ) ≤ (2 : ℝ) ^ N := by positivity
  nlinarith

private theorem norm_integral_ker_mul_sub_le {lam : ℕ → ℝ} (h : KernelGood lam) {g : ℝ → ℂ} (hg : Continuous g) {Mg : ℝ}
    (hMg : ∀ t, ‖g t‖ ≤ Mg) {η r : ℝ} (hr : 0 < r) (hη : ∀ t : ℝ, |t| < r → ‖g t - g 0‖ ≤ η) :
    ‖(∫ t, ((ker lam t : ℝ) : ℂ) * g t) - g 0‖
      ≤ η * (2 * CB + CB / 4) + (2 * Mg * (CB * (3 / 2) * (2 / r)) * 4) / lam 0 := by
  have hlpos := h.pos 0
  have hMg0 : 0 ≤ Mg := (norm_nonneg _).trans (hMg 0)
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη 0 (by simpa using hr))
  set K := ∑' i, kb lam 0 i with hK
  have hKnn : 0 ≤ K := tsum_nonneg (kb_nonneg h 0)
  set V := CB * (3 / 2) * (2 / r) with hV
  have hVnn : 0 ≤ V := by have := CB_pos; positivity

  have hkerC : Integrable (fun t => ((ker lam t : ℝ) : ℂ)) := (integrable_ker h).ofReal
  have hkg : Integrable (fun t => ((ker lam t : ℝ) : ℂ) * g t) :=
    hkerC.mul_bdd (c := Mg) hg.aestronglyMeasurable (Eventually.of_forall hMg)
  have hkg0 : Integrable (fun t => ((ker lam t : ℝ) : ℂ) * g 0) := hkerC.mul_const _

  have hone : ∫ t, ((ker lam t : ℝ) : ℂ) = 1 := by
    rw [integral_complex_ofReal, integral_ker h, Complex.ofReal_one]
  have hsplit : (∫ t, ((ker lam t : ℝ) : ℂ) * g t) - g 0 = ∫ t, ((ker lam t : ℝ) : ℂ) * (g t - g 0) := by
    have : g 0 = ∫ t, ((ker lam t : ℝ) : ℂ) * g 0 := by rw [integral_mul_const, hone, one_mul]
    conv_lhs => rw [this]
    rw [← integral_sub hkg hkg0]
    congr 1; funext t; ring
  rw [hsplit]

  set bound : ℝ → ℝ := fun t => η * (K * Real.exp (-(lam 0 * |t|))) + (2 * Mg * V) * Real.exp (-(lam 0 * |t| / 2))
    with hbound
  have hbound_int : Integrable bound :=
    ((integrable_exp_neg_mul_abs hlpos).const_mul K |>.const_mul η).add
      ((integrable_exp_neg_mul_abs_half hlpos).const_mul _)
  have hpt : ∀ t, ‖((ker lam t : ℝ) : ℂ) * (g t - g 0)‖ ≤ bound t := by
    intro t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hA : 0 ≤ η * (K * Real.exp (-(lam 0 * |t|))) := by positivity
    have hB : 0 ≤ (2 * Mg * V) * Real.exp (-(lam 0 * |t| / 2)) := by positivity
    by_cases ht : |t| < r
    ·
      have h1 := abs_ker_le_exp h t
      calc |ker lam t| * ‖g t - g 0‖ ≤ (K * Real.exp (-(lam 0 * |t|))) * η :=
            mul_le_mul h1 (hη t ht) (norm_nonneg _) (by positivity)
        _ = η * (K * Real.exp (-(lam 0 * |t|))) := by ring
        _ ≤ bound t := by simp only [hbound]; linarith
    ·
      push Not at ht
      have h1 := abs_ker_le_tail_exp h hr ht
      have h2 : ‖g t - g 0‖ ≤ 2 * Mg := by
        calc ‖g t - g 0‖ ≤ ‖g t‖ + ‖g 0‖ := norm_sub_le _ _
          _ ≤ Mg + Mg := add_le_add (hMg t) (hMg 0)
          _ = 2 * Mg := by ring
      calc |ker lam t| * ‖g t - g 0‖ ≤ (V * Real.exp (-(lam 0 * |t| / 2))) * (2 * Mg) :=
            mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
        _ = (2 * Mg * V) * Real.exp (-(lam 0 * |t| / 2)) := by ring
        _ ≤ bound t := by simp only [hbound]; linarith

  have hint : ∫ t, bound t = η * (K * (2 / lam 0)) + (2 * Mg * V) * (4 / lam 0) := by
    simp only [hbound]
    rw [integral_add (((integrable_exp_neg_mul_abs hlpos).const_mul K).const_mul η)
      ((integrable_exp_neg_mul_abs_half hlpos).const_mul _), integral_const_mul, integral_const_mul, integral_const_mul,
      integral_exp_neg_mul_abs hlpos, integral_exp_neg_mul_abs_half hlpos]
  calc ‖∫ t, ((ker lam t : ℝ) : ℂ) * (g t - g 0)‖ ≤ ∫ t, bound t :=
        norm_integral_le_of_norm_le hbound_int (Eventually.of_forall hpt)
    _ = η * (K * (2 / lam 0)) + (2 * Mg * V) * (4 / lam 0) := hint
    _ ≤ η * (2 * CB + CB / 4) + (2 * Mg * V * 4) / lam 0 := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (tsum_kb_mul_integral_le h) hη0
        · exact le_of_eq (by ring)

private theorem tendsto_integral_ker_shiftN_mul {lam : ℕ → ℝ} (h : KernelGood lam) {g : ℝ → ℂ} (hg : Continuous g) {Mg : ℝ}
    (hMg : ∀ t, ‖g t‖ ≤ Mg) :
    Tendsto (fun N => ∫ t, ((ker (shiftN N lam) t : ℝ) : ℂ) * g t) atTop (𝓝 (g 0)) := by
  have hCB := CB_pos
  have hMg0 : 0 ≤ Mg := (norm_nonneg _).trans (hMg 0)
  rw [Metric.tendsto_atTop]
  intro ε hε

  set K' : ℝ := 2 * CB + CB / 4 with hK'
  have hK'pos : 0 < K' := by positivity
  set η : ℝ := ε / 2 / K' with hηdef
  have hηpos : 0 < η := by positivity

  obtain ⟨r, hr, hgr⟩ : ∃ r > 0, ∀ t : ℝ, |t| < r → ‖g t - g 0‖ ≤ η := by
    have hc := Metric.continuousAt_iff.1 (hg.continuousAt (x := 0))
    obtain ⟨r, hr, hball⟩ := hc η hηpos
    refine ⟨r, hr, fun t ht => ?_⟩
    have : dist t 0 < r := by rwa [Real.dist_eq, sub_zero]
    have := hball this
    rw [dist_eq_norm] at this
    exact this.le
  set c : ℝ := 2 * Mg * (CB * (3 / 2) * (2 / r)) * 4 with hcdef
  have hc0 : 0 ≤ c := by positivity

  refine ⟨Nat.ceil (4 * c / ε) + 1, fun N hN => ?_⟩
  have hμ : KernelGood (shiftN N lam) := h.shiftN N
  have hest := norm_integral_ker_mul_sub_le hμ hg hMg hr hgr
  rw [shiftN_apply, Nat.zero_add] at hest
  rw [dist_eq_norm]

  have hfirst : η * K' = ε / 2 := by rw [hηdef]; field_simp

  have hlamN : (4 * c / ε) < lam N := by
    have h1 : (4 * c / ε) ≤ (Nat.ceil (4 * c / ε) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (4 * c / ε) : ℕ) : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hN
    have h3 := nat_le_lam h N
    linarith
  have hlamNpos : 0 < lam N := h.pos N
  have hsecond : c / lam N ≤ ε / 4 := by
    rw [div_le_iff₀ hlamNpos]
    have : 4 * c / ε * ε = 4 * c := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hlamN.le hε.le]
  calc ‖(∫ t, ((ker (shiftN N lam) t : ℝ) : ℂ) * g t) - g 0‖ ≤ η * K' + c / lam N := hest
    _ = ε / 2 + c / lam N := by rw [hfirst]
    _ ≤ ε / 2 + ε / 4 := by linarith
    _ < ε := by linarith

end OneVariableFactorization
p2m_reactivate "P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.OneVariableFactorization"

namespace OneVariableFactorization
namespace Operators

open OneVariableFactorization

private def growthFloor : (N : ℕ) → (Fin N → ℝ) → ℝ
  | 0, _ => 4
  | N + 1, p => 2 * (1 / p (Fin.last N))

private def productFloor (N : ℕ) (p : Fin N → ℝ) : ℝ := (4 : ℝ) ^ N * ∏ j : Fin N, (1 / p j) ^ 2

private def masterPrefix (Bs : ℕ → ℝ) : (N : ℕ) → (Fin N → ℝ) → ℝ
  | 0, _ => 0
  | N + 1, p =>
    (4 / 3 : ℝ) ^ (N + 1 + 1) * (∏ j : Fin (N + 1), 1 / (1 / p j) ^ 2) * (8 : ℝ) ^ (N + 1 + 1)
      * Bs (3 * (N + 1) + 3) * (1 / p (Fin.last N)) ^ (3 * (N + 1) + 3)

private def stageFloor (Bs : ℕ → ℝ) (indexFloor : ℕ → ℝ) (N : ℕ) (p : Fin N → ℝ) : ℝ :=
  max 1 (max (max (growthFloor N p) (productFloor N p))
    (max (indexFloor N) (|masterPrefix Bs N p| * (2 : ℝ) ^ (N + 1))))

private theorem one_le_stageFloor (Bs indexFloor : ℕ → ℝ) (N : ℕ) (p : Fin N → ℝ) :
    1 ≤ stageFloor Bs indexFloor N p := le_max_left _ _

private theorem growthFloor_le_stageFloor (Bs indexFloor : ℕ → ℝ) (N : ℕ) (p : Fin N → ℝ) :
    growthFloor N p ≤ stageFloor Bs indexFloor N p :=
  le_max_of_le_right (le_max_of_le_left (le_max_left _ _))

private theorem productFloor_le_stageFloor (Bs indexFloor : ℕ → ℝ) (N : ℕ) (p : Fin N → ℝ) :
    productFloor N p ≤ stageFloor Bs indexFloor N p :=
  le_max_of_le_right (le_max_of_le_left (le_max_right _ _))

private theorem indexFloor_le_stageFloor (Bs indexFloor : ℕ → ℝ) (N : ℕ) (p : Fin N → ℝ) :
    indexFloor N ≤ stageFloor Bs indexFloor N p :=
  le_max_of_le_right (le_max_of_le_right (le_max_left _ _))

private theorem masterPrefix_le_stageFloor (Bs indexFloor : ℕ → ℝ) (N : ℕ) (p : Fin N → ℝ) :
    |masterPrefix Bs N p| * (2 : ℝ) ^ (N + 1) ≤ stageFloor Bs indexFloor N p :=
  le_max_of_le_right (le_max_of_le_right (le_max_right _ _))

private theorem exists_indexFloor {δ : ℝ} (hδ : 0 < δ) (Bs : ℕ → ℝ) (i : ℕ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      CB * Bs (3 * i + 3) * x ^ (3 * i + 3) * Real.exp (-(x * δ / 2)) ≤ (1 / 2 : ℝ) ^ i := by
  set n : ℕ := 3 * i + 3
  have hlin : Tendsto (fun x : ℝ => x * δ / 2) atTop atTop :=
    (tendsto_id.atTop_mul_const hδ).atTop_div_const two_pos
  have h0 : Tendsto (fun x : ℝ => (x * δ / 2) ^ n * Real.exp (-(x * δ / 2))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp hlin
  have h1 : Tendsto (fun x : ℝ => (CB * Bs n * (2 / δ) ^ n) * ((x * δ / 2) ^ n * Real.exp (-(x * δ / 2))))
      atTop (𝓝 ((CB * Bs n * (2 / δ) ^ n) * 0)) := h0.const_mul _
  rw [mul_zero] at h1
  have hx : ∀ x : ℝ, (2 / δ) ^ n * (x * δ / 2) ^ n = x ^ n := by
    intro x
    have hδ0 : δ ≠ 0 := hδ.ne'
    rw [← mul_pow]
    congr 1
    field_simp
  have hg : Tendsto (fun x : ℝ => CB * Bs n * x ^ n * Real.exp (-(x * δ / 2))) atTop (𝓝 0) := by
    refine h1.congr fun x => ?_
    rw [← hx x]
    ring
  have hev : ∀ᶠ x : ℝ in atTop, CB * Bs n * x ^ n * Real.exp (-(x * δ / 2)) < (1 / 2 : ℝ) ^ i :=
    hg.eventually (gt_mem_nhds (by positivity))
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  exact ⟨X, fun x hx' => (hX x hx').le⟩

private theorem exists_thr {δ : ℝ} (hδ : 0 < δ) (Bs : ℕ → ℝ) :
    ∃ thr : (N : ℕ) → (Fin N → ℝ) → ℝ, (∀ N p, 0 < thr N p) ∧
      ∀ a : ℕ → ℝ, (∀ N, 0 < a N ∧ a N ≤ thr N (fun i : Fin N => a i)) →
        KernelGood (fun n => 1 / a n) ∧ MasterGood δ Bs (fun n => 1 / a n) := by
  choose indexFloor hindexFloor using fun i => exists_indexFloor hδ Bs i
  refine ⟨fun N p => 1 / stageFloor Bs indexFloor N p, fun N p => ?_, fun a ha => ?_⟩
  · exact one_div_pos.mpr (lt_of_lt_of_le one_pos (one_le_stageFloor Bs indexFloor N p))
  have hapos : ∀ N, 0 < a N := fun N => (ha N).1
  have hXpos : ∀ N, 0 < stageFloor Bs indexFloor N (fun i : Fin N => a i) := fun N =>
    lt_of_lt_of_le one_pos (one_le_stageFloor Bs indexFloor N _)

  have hX : ∀ N, stageFloor Bs indexFloor N (fun i : Fin N => a i) ≤ 1 / a N := fun N =>
    (le_one_div (hapos N) (hXpos N)).mp (ha N).2
  have hlam1 : ∀ N, 1 ≤ 1 / a N := fun N => (one_le_stageFloor Bs indexFloor N _).trans (hX N)
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩⟩
  ·
    have h := (growthFloor_le_stageFloor Bs indexFloor 0 (fun i : Fin 0 => a i)).trans (hX 0)
    simp only [growthFloor] at h
    exact h
  ·
    intro n
    have h := (growthFloor_le_stageFloor Bs indexFloor (n + 1) (fun i : Fin (n + 1) => a i)).trans (hX (n + 1))
    simp only [growthFloor, Fin.val_last] at h
    exact h
  ·
    intro n
    have h := (productFloor_le_stageFloor Bs indexFloor n (fun i : Fin n => a i)).trans (hX n)
    simp only [productFloor] at h
    rw [Fin.prod_univ_eq_prod_range (fun j => (1 / a j) ^ 2) n] at h
    exact h
  ·
    intro i
    exact hindexFloor i (1 / a i) ((indexFloor_le_stageFloor Bs indexFloor i _).trans (hX i))
  ·
    intro N hN
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    set Q : ℝ := masterPrefix Bs (M + 1) (fun i : Fin (M + 1) => a i) with hQdef
    have hQle : |Q| * (2 : ℝ) ^ (M + 1 + 1) ≤ 1 / a (M + 1) :=
      (masterPrefix_le_stageFloor Bs indexFloor (M + 1) _).trans (hX (M + 1))
    have hta : |Q| * (2 : ℝ) ^ (M + 1 + 1) * a (M + 1) ≤ 1 := (le_div_iff₀ (hapos (M + 1))).mp hQle
    have ha1 : a (M + 1) ≤ 1 := by
      have := (le_div_iff₀ (hapos (M + 1))).mp (hlam1 (M + 1))
      simpa using this
    have key : Q * (1 / (1 / a (M + 1)) ^ 2) ≤ (1 / 2 : ℝ) ^ (M + 1 + 1) := by
      rw [one_div_pow, one_div_one_div, one_div_pow,
        le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (M + 1 + 1))]
      have h1 : Q * (a (M + 1) ^ 2 * (2 : ℝ) ^ (M + 1 + 1)) ≤ |Q| * (a (M + 1) ^ 2 * (2 : ℝ) ^ (M + 1 + 1)) :=
        mul_le_mul_of_nonneg_right (le_abs_self Q) (by positivity)
      have h2 : |Q| * (2 : ℝ) ^ (M + 1 + 1) * a (M + 1) * a (M + 1) ≤ 1 * a (M + 1) :=
        mul_le_mul_of_nonneg_right hta (hapos (M + 1)).le
      nlinarith [h1, h2, ha1]
    rw [Finset.prod_range_succ]
    convert key using 1
    simp only [hQdef, masterPrefix, uOf, Fin.val_last, Nat.add_sub_cancel]
    rw [Fin.prod_univ_eq_prod_range (fun j => 1 / (1 / a j) ^ 2) (M + 1)]
    ring

end OneVariableFactorization.Operators
p2m_reactivate "P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.OneVariableFactorization"
p2m_reactivate "P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.OneVariableFactorization"

namespace OneVariableFactorization
namespace Operators

open OneVariableFactorization

private theorem natCast_lt_coe_top (k : ℕ) : (k : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_lt_coe.mpr (ENat.coe_lt_top k)

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def opSum (u : ℕ → ℝ) (g : ℝ → E) (N : ℕ) : ℝ → E :=
  fun t => ∑ n ∈ range (N + 1), ((-1 : ℝ) ^ n * es u N n) • iteratedDeriv (2 * n) g t

variable {g : ℝ → E} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
include hg

private theorem differentiable_iteratedDeriv_of_smooth (m : ℕ) : Differentiable ℝ (iteratedDeriv m g) :=
  hg.differentiable_iteratedDeriv m (natCast_lt_coe_top m)

private theorem contDiff_iteratedDeriv_of_smooth (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv m g) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv m hg

private theorem deriv_sum_smul_iteratedDeriv (s : Finset ℕ) (c : ℕ → ℝ) (k : ℕ → ℕ) :
    deriv (fun t => ∑ n ∈ s, c n • iteratedDeriv (k n) g t)
      = fun t => ∑ n ∈ s, c n • iteratedDeriv (k n + 1) g t := by
  funext t
  have hfun : (fun t => ∑ n ∈ s, c n • iteratedDeriv (k n) g t) = ∑ n ∈ s, c n • iteratedDeriv (k n) g := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply]
  rw [hfun, deriv_sum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [deriv_const_smul (c n) (differentiable_iteratedDeriv_of_smooth hg (k n) t), iteratedDeriv_succ]
  · intro n _
    exact (differentiable_iteratedDeriv_of_smooth hg (k n) t).const_smul (c n)

private theorem contDiff_opSum (u : ℕ → ℝ) (N : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (opSum u g N) := by
  unfold opSum
  exact ContDiff.sum fun n _ => (contDiff_iteratedDeriv_of_smooth hg (2 * n)).const_smul _

private theorem deriv_deriv_opSum (u : ℕ → ℝ) (N : ℕ) :
    deriv (deriv (opSum u g N))
      = fun t => ∑ n ∈ range (N + 1), ((-1 : ℝ) ^ n * es u N n) • iteratedDeriv (2 * n + 1 + 1) g t := by
  unfold opSum
  rw [deriv_sum_smul_iteratedDeriv hg, deriv_sum_smul_iteratedDeriv hg]

private theorem opSum_of_recursion (u : ℕ → ℝ) (P : ℕ → ℝ → E) (hP0 : P 0 = g)
    (hPsucc : ∀ N, P (N + 1) = fun t => P N t - u N • deriv (deriv (P N)) t) :
    ∀ N, P N = opSum u g N := by
  intro N
  induction N with
  | zero =>
    rw [hP0]
    funext t
    simp [opSum]
  | succ N ih =>
    rw [hPsucc N, ih, deriv_deriv_opSum hg]
    funext t
    simp only [opSum]

    have h2a : ∀ n : ℕ, 2 * (n + 1) = 2 * n + 2 := fun n => by ring
    have h2b : ∀ n : ℕ, 2 * n + 1 + 1 = 2 * n + 2 := fun n => by ring

    rw [Finset.sum_range_succ' (fun n => ((-1 : ℝ) ^ n * es u (N + 1) n) • iteratedDeriv (2 * n) g t)]
    simp only [es_succ_succ, es_succ_zero, h2a]

    rw [Finset.sum_range_succ' (fun n => ((-1 : ℝ) ^ n * es u N n) • iteratedDeriv (2 * n) g t)]
    simp only [h2a, h2b]
    have hext : ∑ n ∈ range N, ((-1 : ℝ) ^ (n + 1) * es u N (n + 1)) • iteratedDeriv (2 * n + 2) g t
        = ∑ n ∈ range (N + 1), ((-1 : ℝ) ^ (n + 1) * es u N (n + 1)) • iteratedDeriv (2 * n + 2) g t := by
      rw [Finset.sum_range_succ, es_eq_zero_of_lt u N (N + 1) (by omega), mul_zero, zero_smul, add_zero]
    rw [hext, Finset.smul_sum]
    have hterm : ∀ n ∈ range (N + 1),
        ((-1 : ℝ) ^ (n + 1) * (es u N (n + 1) + u N * es u N n)) • iteratedDeriv (2 * n + 2) g t
          = ((-1 : ℝ) ^ (n + 1) * es u N (n + 1)) • iteratedDeriv (2 * n + 2) g t
            - u N • (((-1 : ℝ) ^ n * es u N n) • iteratedDeriv (2 * n + 2) g t) := by
      intro n _
      rw [smul_smul, ← sub_smul]
      congr 1
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib]
    abel

private theorem contDiff_of_recursion (u : ℕ → ℝ) (P : ℕ → ℝ → E) (hP0 : P 0 = g)
    (hPsucc : ∀ N, P (N + 1) = fun t => P N t - u N • deriv (deriv (P N)) t) (N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (P N) := by
  rw [opSum_of_recursion hg u P hP0 hPsucc N]
  exact contDiff_opSum hg u N

end Generic
p2m_reactivate "P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.OneVariableFactorization"

private theorem opSum_of_recursion_complex (u : ℕ → ℝ) {F : ℝ → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (P : ℕ → ℝ → ℂ)
    (hP0 : P 0 = F) (hPsucc : ∀ N, P (N + 1) = fun t => P N t - ((u N : ℝ) : ℂ) * deriv (deriv (P N)) t) (N : ℕ) :
    P N = fun t => ∑ n ∈ range (N + 1), ((-1 : ℝ) ^ n * es u N n) • iteratedDeriv (2 * n) F t :=
  opSum_of_recursion hF u P hP0 (fun N => by rw [hPsucc N]; simp only [Complex.real_smul]) N

private theorem contDiff_of_recursion_complex (u : ℕ → ℝ) {F : ℝ → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (P : ℕ → ℝ → ℂ)
    (hP0 : P 0 = F) (hPsucc : ∀ N, P (N + 1) = fun t => P N t - ((u N : ℝ) : ℂ) * deriv (deriv (P N)) t) (N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (P N) :=
  contDiff_of_recursion hF u P hP0 (fun N => by rw [hPsucc N]; simp only [Complex.real_smul]) N

private theorem opSum_of_recursion_real (u : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (P : ℕ → ℝ → ℝ)
    (hP0 : P 0 = f) (hPsucc : ∀ N, P (N + 1) = fun t => P N t - u N * deriv (deriv (P N)) t) (N : ℕ) :
    P N = fun t => ∑ n ∈ range (N + 1), ((-1 : ℝ) ^ n * es u N n) * iteratedDeriv (2 * n) f t := by
  have h := opSum_of_recursion hf u P hP0 (fun N => by rw [hPsucc N]; simp only [smul_eq_mul]) N
  rw [h]
  funext t
  simp only [opSum, smul_eq_mul]

private theorem contDiff_of_recursion_real (u : ℕ → ℝ) {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (P : ℕ → ℝ → ℝ)
    (hP0 : P 0 = f) (hPsucc : ∀ N, P (N + 1) = fun t => P N t - u N * deriv (deriv (P N)) t) (N : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (P N) :=
  contDiff_of_recursion hf u P hP0 (fun N => by rw [hPsucc N]; simp only [smul_eq_mul]) N

section ByParts

open MeasureTheory

private theorem hasCompactSupport_ofReal_comp {g : ℝ → ℝ} (hgs : HasCompactSupport g) :
    HasCompactSupport fun t : ℝ => (g t : ℂ) :=
  hgs.comp_left Complex.ofReal_zero

variable {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
include hg

private theorem contDiff_deriv_of_smooth : ContDiff ℝ (⊤ : ℕ∞) (deriv g) := (contDiff_infty_iff_deriv.mp hg).2

private theorem hasDerivAt_ofReal_comp_of_smooth (t : ℝ) :
    HasDerivAt (fun s : ℝ => (g s : ℂ)) ((deriv g t : ℝ) : ℂ) t :=
  ((contDiff_infty_iff_deriv.mp hg).1 t).hasDerivAt.ofReal_comp

omit hg in
private theorem hasCompactSupport_iteratedDeriv_of_cs (hgs : HasCompactSupport g) :
    ∀ k : ℕ, HasCompactSupport (iteratedDeriv k g)
  | 0 => by simpa using hgs
  | k + 1 => by
    rw [iteratedDeriv_succ]
    exact (hasCompactSupport_iteratedDeriv_of_cs hgs k).deriv

variable {F : ℝ → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
include hF

private theorem integral_ofReal_mul_deriv_eq_neg (hgs : HasCompactSupport g) (m : ℕ) :
    ∫ t, (g t : ℂ) * iteratedDeriv (m + 1) F t = -∫ t, ((deriv g t : ℝ) : ℂ) * iteratedDeriv m F t := by
  have hv : Differentiable ℝ (iteratedDeriv m F) := differentiable_iteratedDeriv_of_smooth hF m
  have hv' : Continuous (iteratedDeriv (m + 1) F) := (differentiable_iteratedDeriv_of_smooth hF (m + 1)).continuous
  have hu_cont : Continuous fun t : ℝ => (g t : ℂ) := Complex.continuous_ofReal.comp hg.continuous
  have hu'_cont : Continuous fun t : ℝ => ((deriv g t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (contDiff_deriv_of_smooth hg).continuous
  have hu_cs : HasCompactSupport fun t : ℝ => (g t : ℂ) := hasCompactSupport_ofReal_comp hgs
  have hu'_cs : HasCompactSupport fun t : ℝ => ((deriv g t : ℝ) : ℂ) := hasCompactSupport_ofReal_comp hgs.deriv
  refine integral_mul_deriv_eq_deriv_mul_of_integrable (u := fun t : ℝ => (g t : ℂ))
    (u' := fun t : ℝ => ((deriv g t : ℝ) : ℂ)) (v := iteratedDeriv m F) (v' := iteratedDeriv (m + 1) F)
    (fun t _ => hasDerivAt_ofReal_comp_of_smooth hg t) (fun t _ => ?_) ?_ ?_ ?_
  · rw [iteratedDeriv_succ]
    exact (hv t).hasDerivAt
  · exact (hu_cont.mul hv').integrable_of_hasCompactSupport hu_cs.mul_right
  · exact (hu'_cont.mul hv.continuous).integrable_of_hasCompactSupport hu'_cs.mul_right
  · exact (hu_cont.mul hv.continuous).integrable_of_hasCompactSupport hu_cs.mul_right

omit hg in

private theorem integral_ofReal_mul_iteratedDeriv_eq (n : ℕ) :
    ∀ (g : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      ∫ t, (g t : ℂ) * iteratedDeriv (2 * n) F t = ∫ t, ((iteratedDeriv (2 * n) g t : ℝ) : ℂ) * F t := by
  induction n with
  | zero =>
    intro g _ _
    simp
  | succ n ih =>
    intro g hg hgs
    have h2 : 2 * (n + 1) = 2 * n + 1 + 1 := by ring
    have e2 : iteratedDeriv (2 * n + 1 + 1) g = iteratedDeriv (2 * n) (deriv (deriv g)) := by
      rw [iteratedDeriv_succ', iteratedDeriv_succ']
    rw [h2, e2, integral_ofReal_mul_deriv_eq_neg hg hF hgs (2 * n + 1),
      integral_ofReal_mul_deriv_eq_neg (contDiff_deriv_of_smooth hg) hF hgs.deriv (2 * n), neg_neg]
    exact ih (deriv (deriv g)) (contDiff_deriv_of_smooth (contDiff_deriv_of_smooth hg)) hgs.deriv.deriv

private theorem integral_ofReal_mul_recursion_eq (hgs : HasCompactSupport g) (u : ℕ → ℝ) (P : ℕ → ℝ → ℂ) (hP0 : P 0 = F)
    (hPsucc : ∀ N, P (N + 1) = fun t => P N t - ((u N : ℝ) : ℂ) * deriv (deriv (P N)) t) (Q : ℕ → ℝ → ℝ)
    (hQ0 : Q 0 = g) (hQsucc : ∀ N, Q (N + 1) = fun t => Q N t - u N * deriv (deriv (Q N)) t) (N : ℕ) :
    ∫ t, (g t : ℂ) * P N t = ∫ t, ((Q N t : ℝ) : ℂ) * F t := by
  rw [opSum_of_recursion_complex u hF P hP0 hPsucc N, opSum_of_recursion_real u hg Q hQ0 hQsucc N]
  have hDF : ∀ k : ℕ, Continuous (iteratedDeriv k F) := fun k =>
    (differentiable_iteratedDeriv_of_smooth hF k).continuous
  have hDg : ∀ k : ℕ, Continuous (iteratedDeriv k g) := fun k =>
    (differentiable_iteratedDeriv_of_smooth hg k).continuous
  have hL : ∫ t, (g t : ℂ) * ∑ n ∈ range (N + 1), ((-1 : ℝ) ^ n * es u N n) • iteratedDeriv (2 * n) F t
      = ∑ n ∈ range (N + 1), (((-1 : ℝ) ^ n * es u N n : ℝ) : ℂ) * ∫ t, (g t : ℂ) * iteratedDeriv (2 * n) F t := by
    simp_rw [Complex.real_smul, Finset.mul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [← integral_const_mul]
      congr 1
      funext t
      ring
    · intro n _
      refine Continuous.integrable_of_hasCompactSupport
        ((Complex.continuous_ofReal.comp hg.continuous).mul (continuous_const.mul (hDF (2 * n)))) ?_
      exact (hasCompactSupport_ofReal_comp hgs).mul_right
  have hR : ∫ t, ((∑ n ∈ range (N + 1), ((-1 : ℝ) ^ n * es u N n) * iteratedDeriv (2 * n) g t : ℝ) : ℂ) * F t
      = ∑ n ∈ range (N + 1),
          (((-1 : ℝ) ^ n * es u N n : ℝ) : ℂ) * ∫ t, ((iteratedDeriv (2 * n) g t : ℝ) : ℂ) * F t := by
    simp_rw [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [← integral_const_mul]
      congr 1
      funext t
      ring
    · intro n _
      refine Continuous.integrable_of_hasCompactSupport
        ((continuous_const.mul (Complex.continuous_ofReal.comp (hDg (2 * n)))).mul hF.continuous) ?_
      exact ((hasCompactSupport_ofReal_comp (hasCompactSupport_iteratedDeriv_of_cs hgs (2 * n))).mul_left).mul_right
  rw [hL, hR]
  exact Finset.sum_congr rfl fun n _ => by rw [integral_ofReal_mul_iteratedDeriv_eq hF n g hg hgs]

end ByParts
p2m_reactivate "P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.OneVariableFactorization"

end OneVariableFactorization.Operators
p2m_reactivate "P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.OneVariableFactorization"
p2m_reactivate "P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.OneVariableFactorization"

namespace OneVariableFactorization

open Finset Filter Topology MeasureTheory

private theorem iteratedDeriv_eq_zero_of_eqOn_zero {U : Set ℝ} (hU : IsOpen U) :
    ∀ (j : ℕ) (f : ℝ → ℝ), Set.EqOn f (fun _ => (0 : ℝ)) U → ∀ t ∈ U, iteratedDeriv j f t = 0
  | 0, f, hf, t, ht => by rw [iteratedDeriv_zero]; exact hf ht
  | j + 1, f, hf, t, ht => by
    rw [iteratedDeriv_succ']
    refine iteratedDeriv_eq_zero_of_eqOn_zero hU j (deriv f) (fun s hs => ?_) t ht
    have hev : f =ᶠ[𝓝 s] fun _ => (0 : ℝ) := eventuallyEq_of_mem (hU.mem_nhds hs) hf
    show deriv f s = 0
    rw [hev.deriv_eq, deriv_const]

private theorem iteratedDeriv_eq_zero_of_eqOn_const {U : Set ℝ} (hU : IsOpen U) {f : ℝ → ℝ} {c : ℝ}
    (hf : Set.EqOn f (fun _ => c) U) (j : ℕ) (hj : 1 ≤ j) {t : ℝ} (ht : t ∈ U) : iteratedDeriv j f t = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [iteratedDeriv_succ']
  refine iteratedDeriv_eq_zero_of_eqOn_zero hU k (deriv f) (fun s hs => ?_) t ht
  have hev : f =ᶠ[𝓝 s] fun _ => c := eventuallyEq_of_mem (hU.mem_nhds hs) hf
  show deriv f s = 0
  rw [hev.deriv_eq, deriv_const]

private theorem isOpen_abs_lt (r : ℝ) : IsOpen {t : ℝ | |t| < r} := isOpen_lt continuous_abs continuous_const

private theorem isOpen_lt_abs (r : ℝ) : IsOpen {t : ℝ | r < |t|} := isOpen_lt continuous_const continuous_abs

private theorem exists_bound_of_continuous_of_outer {δ : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hout : ∀ t : ℝ, δ < |t| → f t = 0) : ∃ B, ∀ t, |f t| ≤ B := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (-δ) δ) hf.continuousOn
  refine ⟨max C 0, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (-δ) δ
  · exact (Real.norm_eq_abs (f t) ▸ hC t ht).trans (le_max_left _ _)
  · have hδt : δ < |t| := by
      rw [Set.mem_Icc] at ht
      rcases lt_or_ge δ |t| with hlt | hge
      · exact hlt
      · exact absurd (abs_le.1 hge) ht
    rw [hout t hδt, abs_zero]
    exact le_max_right _ _

private theorem exists_cutoff {δ : ℝ} (hδ : 0 < δ) : ∃ (θ : ℝ → ℝ) (Bs : ℕ → ℝ), CutoffData δ Bs θ ∧ θ 0 = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨δ / 2, 3 * δ / 4, by positivity, by linarith⟩
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun t => b t) := b.contDiff

  have hone : Set.EqOn (fun t => b t) (fun _ => (1 : ℝ)) {t : ℝ | |t| < δ / 2} := by
    intro t ht
    show b t = 1
    apply b.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact (Set.mem_setOf_eq ▸ ht).le

  have hzero : Set.EqOn (fun t => b t) (fun _ => (0 : ℝ)) {t : ℝ | δ < |t|} := by
    intro t ht
    show b t = 0
    apply b.zero_of_le_dist
    rw [Real.dist_eq, sub_zero]
    have : δ < |t| := ht
    show 3 * δ / 4 ≤ |t|
    linarith
  have houter : ∀ (j : ℕ) (t : ℝ), δ < |t| → iteratedDeriv j (fun t => b t) t = 0 :=
    fun j t ht => iteratedDeriv_eq_zero_of_eqOn_zero (isOpen_lt_abs δ) j _ hzero t ht

  have hbdd : ∀ j : ℕ, ∃ B, ∀ t, |iteratedDeriv j (fun t => b t) t| ≤ B := fun j =>
    exists_bound_of_continuous_of_outer (contDiff_iteratedDeriv_of_top hsmooth j).continuous (houter j)
  choose B hB using hbdd
  refine ⟨fun t => b t, fun j => ∑ i ∈ range (j + 1), |B i|, ⟨hsmooth, ?_, houter, ?_, ?_⟩, ?_⟩
  · intro j hj t ht
    exact iteratedDeriv_eq_zero_of_eqOn_const (isOpen_abs_lt (δ / 2)) hone j hj ht
  · intro j t
    calc |iteratedDeriv j (fun t => b t) t| ≤ B j := hB j t
      _ ≤ |B j| := le_abs_self _
      _ ≤ ∑ i ∈ range (j + 1), |B i| := single_le_sum (fun i _ => abs_nonneg (B i)) (mem_range.2 (Nat.lt_succ_self j))
  · intro j k hjk
    exact sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (by omega)) (fun i _ _ => abs_nonneg (B i))
  · show b 0 = 1
    exact b.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity))

private theorem theta_eq_zero_of_outer {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ} (hc : CutoffData δ Bs θ) {t : ℝ} (ht : δ < |t|) :
    θ t = 0 := by
  have := hc.outer 0 t ht
  rwa [iteratedDeriv_zero] at this

private abbrev lamOf (a : ℕ → ℝ) : ℕ → ℝ := fun n => 1 / a n

private theorem uOf_lamOf (a : ℕ → ℝ) (N : ℕ) (hN : a N ≠ 0) : uOf (lamOf a) N = (a N) ^ 2 := uOf_one_div a N hN

private theorem hasCompactSupport_of_outer {E : Type*} [Zero E] {δ : ℝ} {f : ℝ → E} (hf : ∀ t : ℝ, δ < |t| → f t = 0) :
    HasCompactSupport f :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport f) (tsupport_subset_Icc_of_outer hf)

private theorem exists_bound_theta_mul {δ : ℝ} {Bs : ℕ → ℝ} {θ : ℝ → ℝ} (hc : CutoffData δ Bs θ) {F : ℝ → ℂ}
    (hF : Continuous F) : ∃ Mg, ∀ t, ‖((θ t : ℝ) : ℂ) * F t‖ ≤ Mg := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Set.Icc (-δ) δ)
    ((Complex.continuous_ofReal.comp hc.smooth.continuous).mul hF).continuousOn
  refine ⟨max C 0, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (-δ) δ
  · exact (hC t ht).trans (le_max_left _ _)
  · have hδt : δ < |t| := by
      rw [Set.mem_Icc] at ht
      rcases lt_or_ge δ |t| with hlt | hge
      · exact hlt
      · exact absurd (abs_le.1 hge) ht
    rw [theta_eq_zero_of_outer hc hδt, Complex.ofReal_zero, zero_mul, norm_zero]
    exact le_max_right _ _

private theorem tendsto_integral_cutoff_ker_mul_recursion {a : ℕ → ℝ} (ha : ∀ N, 0 < a N) {δ : ℝ} (hδ : 0 < δ)
    {Bs : ℕ → ℝ} {θ : ℝ → ℝ} (hc : CutoffData δ Bs θ) (hθ0 : θ 0 = 1) (h : KernelGood (lamOf a))
    (hm : MasterGood δ Bs (lamOf a)) (F : ℝ → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (P : ℕ → ℝ → ℂ) (hP0 : P 0 = F)
    (hPsucc : ∀ N, P (N + 1) = fun t => P N t - (((a N) ^ 2 : ℝ) : ℂ) * deriv (deriv (P N)) t) :
    Tendsto (fun N : ℕ => ∫ (t : ℝ), ((θ t * ker (lamOf a) t : ℝ) : ℂ) * P N t) atTop
      (𝓝 (F 0 + ∫ (t : ℝ), ((psi (lamOf a) θ t : ℝ) : ℂ) * F t)) := by

  have hP' : ∀ N, P (N + 1) = fun t => P N t - ((uOf (lamOf a) N : ℝ) : ℂ) * deriv (deriv (P N)) t := by
    intro N
    rw [hPsucc N, uOf_lamOf a N (ha N).ne']

  set g : ℝ → ℝ := fun t => θ t * ker (lamOf a) t with hg_def
  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := hc.smooth.mul (contDiff_ker h)
  have hg_cs : HasCompactSupport g :=
    hasCompactSupport_of_outer (δ := δ) (fun t (ht : δ < |t|) => by
      simp only [hg_def, theta_eq_zero_of_outer hc ht, zero_mul])
  let Q : ℕ → ℝ → ℝ := fun N => Nat.rec g (fun N QN => fun t => QN t - uOf (lamOf a) N * deriv (deriv QN) t) N
  have hQ0 : Q 0 = g := rfl
  have hQsucc : ∀ N, Q (N + 1) = fun t => Q N t - uOf (lamOf a) N * deriv (deriv (Q N)) t := fun _ => rfl

  have hO2 := fun N : ℕ =>
    OneVariableFactorization.Operators.integral_ofReal_mul_recursion_eq hg_smooth hF hg_cs (uOf (lamOf a)) P hP0 hP' Q hQ0 hQsucc N

  have hO1 : ∀ N, Q N = fun t => ∑ n ∈ range (N + 1), ((-1 : ℝ) ^ n * es (uOf (lamOf a)) N n) *
      iteratedDeriv (2 * n) g t := fun N =>
    OneVariableFactorization.Operators.opSum_of_recursion_real (uOf (lamOf a)) hg_smooth Q hQ0 hQsucc N
  have hK : ∀ N, ker (shiftN N (lamOf a)) = fun t => ∑ n ∈ range (N + 1), ((-1 : ℝ) ^ n * es (uOf (lamOf a)) N n) *
      iteratedDeriv (2 * n) (ker (lamOf a)) t := fun N =>
    OneVariableFactorization.Operators.opSum_of_recursion_real (uOf (lamOf a)) (contDiff_ker h) (fun N => ker (shiftN N (lamOf a))) rfl
      (ker_shiftN_recursion h) N

  have hsplit : ∀ N t, Q N t = psiN (lamOf a) θ N t + θ t * ker (shiftN N (lamOf a)) t := by
    intro N t
    rw [hO1 N, hK N, psiN_eq]
    try simp only
    have hg_eq : g = θ * ker (lamOf a) := rfl
    rw [hg_eq]
    have hkd : ∀ n, iteratedDeriv (2 * n) (ker (lamOf a)) t = kerD (lamOf a) (2 * n) t := fun n => by
      rw [iteratedDeriv_two_mul_ker h n]
    simp only [hkd]
    ring

  have hθF_cont : Continuous (fun t => ((θ t : ℝ) : ℂ) * F t) :=
    (Complex.continuous_ofReal.comp hc.smooth.continuous).mul hF.continuous
  obtain ⟨Mg, hMg⟩ := exists_bound_theta_mul hc hF.continuous
  have hI1 : ∀ N, Integrable (fun t => ((ker (shiftN N (lamOf a)) t : ℝ) : ℂ) * (((θ t : ℝ) : ℂ) * F t)) := fun N =>
    (integrable_ker (h.shiftN N)).ofReal.mul_bdd (c := Mg) hθF_cont.aestronglyMeasurable (Eventually.of_forall hMg)
  have hpsiN_cont : ∀ N, Continuous (fun t => psiN (lamOf a) θ N t) := fun N => by
    simp only [psiN]
    exact continuous_finsetSum _ (fun n _ => continuous_const.mul (contDiff_rgroup h hc n).continuous)
  have hcont2 : ∀ N, Continuous (fun t => ((psiN (lamOf a) θ N t : ℝ) : ℂ) * F t) := fun N =>
    (Complex.continuous_ofReal.comp (hpsiN_cont N)).mul hF.continuous
  have hI2 : ∀ N, Integrable (fun t => ((psiN (lamOf a) θ N t : ℝ) : ℂ) * F t) := fun N =>
    (hcont2 N).integrable_of_hasCompactSupport
      (hasCompactSupport_of_outer (δ := δ) (fun t (ht : δ < |t|) => by
        show ((psiN (lamOf a) θ N t : ℝ) : ℂ) * F t = 0
        rw [psiN_eq_zero_of_outer h hc N ht, Complex.ofReal_zero, zero_mul]))
  have hdecomp : ∀ N, ∫ (t : ℝ), ((θ t * ker (lamOf a) t : ℝ) : ℂ) * P N t
      = (∫ (t : ℝ), ((ker (shiftN N (lamOf a)) t : ℝ) : ℂ) * (((θ t : ℝ) : ℂ) * F t))
        + ∫ (t : ℝ), ((psiN (lamOf a) θ N t : ℝ) : ℂ) * F t := by
    intro N

    refine (hO2 N).trans ?_
    rw [← integral_add (hI1 N) (hI2 N)]
    congr 1
    funext t
    rw [hsplit N t]
    push_cast
    ring
  simp_rw [hdecomp]

  have hlim1 : Tendsto (fun N => ∫ (t : ℝ), ((ker (shiftN N (lamOf a)) t : ℝ) : ℂ) * (((θ t : ℝ) : ℂ) * F t)) atTop
      (𝓝 (F 0)) := by
    have := tendsto_integral_ker_shiftN_mul h hθF_cont hMg
    simpa [hθ0] using this
  have hlim2 : Tendsto (fun N => ∫ (t : ℝ), ((psiN (lamOf a) θ N t : ℝ) : ℂ) * F t) atTop
      (𝓝 (∫ (t : ℝ), ((psi (lamOf a) θ t : ℝ) : ℂ) * F t)) := by

    set bound : ℝ → ℝ := (Set.Icc (-δ) δ).indicator (fun t => mast0 (lamOf a) δ Bs * ‖F t‖) with hbound
    have hbound_int : Integrable bound := by
      rw [hbound, integrable_indicator_iff measurableSet_Icc]
      exact (hF.continuous.norm.const_mul _).continuousOn.integrableOn_compact isCompact_Icc
    refine tendsto_integral_of_dominated_convergence bound (fun N => ?_) hbound_int (fun N => ?_) ?_
    · exact (hcont2 N).aestronglyMeasurable
    · refine Eventually.of_forall (fun t => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      by_cases ht : t ∈ Set.Icc (-δ) δ
      · rw [hbound, Set.indicator_of_mem ht]
        exact mul_le_mul_of_nonneg_right (abs_psiN_le h hδ hc hm N t) (norm_nonneg _)
      · have hδt : δ < |t| := by
          rw [Set.mem_Icc] at ht
          rcases lt_or_ge δ |t| with hlt | hge
          · exact hlt
          · exact absurd (abs_le.1 hge) ht
        simp only [hbound, Set.indicator_of_notMem ht, psiN_eq_zero_of_outer h hc N hδt, abs_zero, zero_mul, le_refl]
    · refine Eventually.of_forall (fun t => ?_)
      exact ((Complex.continuous_ofReal.tendsto _).comp (tendsto_psiN h hδ hc hm t)).mul_const _
  exact hlim1.add hlim2

private theorem dm_real_assembled (δ : ℝ) (hδ : 0 < δ) :
    ∃ thr : (N : ℕ) → (Fin N → ℝ) → ℝ, (∀ N p, 0 < thr N p) ∧
      ∀ a : ℕ → ℝ, (∀ N, 0 < a N ∧ a N ≤ thr N (fun i : Fin N => a i)) →
        ∃ φ ψ : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
          tsupport φ ⊆ Set.Icc (-δ) δ ∧ tsupport ψ ⊆ Set.Icc (-δ) δ ∧
          ∀ F : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → ∀ P : ℕ → ℝ → ℂ, P 0 = F →
            (∀ N, P (N + 1) = fun t => P N t - (((a N) ^ 2 : ℝ) : ℂ) * deriv (deriv (P N)) t) →
              Filter.Tendsto (fun N : ℕ => ∫ t, φ t * P N t) Filter.atTop
                (nhds (F 0 + ∫ t, ψ t * F t)) := by
  obtain ⟨θ, Bs, hc, hθ0⟩ := exists_cutoff hδ
  obtain ⟨thr, hthr_pos, hthr⟩ := OneVariableFactorization.Operators.exists_thr hδ Bs
  refine ⟨thr, hthr_pos, fun a ha => ?_⟩
  obtain ⟨h, hm⟩ : KernelGood (lamOf a) ∧ MasterGood δ Bs (lamOf a) := hthr a ha
  have ha' : ∀ N, 0 < a N := fun N => (ha N).1
  refine ⟨fun t => ((θ t * ker (lamOf a) t : ℝ) : ℂ), fun t => ((psi (lamOf a) θ t : ℝ) : ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · have := Complex.ofRealCLM.contDiff.comp (hc.smooth.mul (contDiff_ker h))
    simpa [Function.comp_def] using this
  · have := Complex.ofRealCLM.contDiff.comp (contDiff_psi h hδ hc hm)
    simpa [Function.comp_def] using this
  · exact tsupport_subset_Icc_of_outer (fun t ht => by
      rw [theta_eq_zero_of_outer hc ht, zero_mul, Complex.ofReal_zero])
  · exact tsupport_subset_Icc_of_outer (fun t ht => by rw [psi_eq_zero_of_outer h hc ht, Complex.ofReal_zero])
  · intro F hF P hP0 hPsucc
    exact tendsto_integral_cutoff_ker_mul_recursion ha' hδ hc hθ0 h hm F hF P hP0 hPsucc

end OneVariableFactorization
p2m_reactivate "P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.OneVariableFactorization"

end
p2m_reactivate "P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul.OneVariableFactorization"

theorem solution (δ : ℝ) (hδ : 0 < δ) :
    ∃ thr : (N : ℕ) → (Fin N → ℝ) → ℝ, (∀ N p, 0 < thr N p) ∧
      ∀ a : ℕ → ℝ, (∀ N, 0 < a N ∧ a N ≤ thr N (fun i : Fin N => a i)) →
        ∃ φ ψ : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ ContDiff ℝ (⊤ : ℕ∞) ψ ∧
          tsupport φ ⊆ Set.Icc (-δ) δ ∧ tsupport ψ ⊆ Set.Icc (-δ) δ ∧
          ∀ F : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → ∀ P : ℕ → ℝ → ℂ, P 0 = F →
            (∀ N, P (N + 1) = fun t => P N t - (((a N) ^ 2 : ℝ) : ℂ) * deriv (deriv (P N)) t) →
              Filter.Tendsto (fun N : ℕ => ∫ t, φ t * P N t) Filter.atTop
                (nhds (F 0 + ∫ t, ψ t * F t)) := by
  exact OneVariableFactorization.dm_real_assembled δ hδ

end S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul
end P2MW
export P2MW.S_DixmierMalliavin_exists_contDiff_tendsto_integral_mul (solution)
