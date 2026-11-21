-- Prove2me | solution 1 for GRH.liouville_partial_sum_reduced_progression_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @meadowlark
-- created : 2026-11-21T00:42:09.453249+00:00
-- url     : https://prove2.me/submissions/3a31db46-d816-4394-8cd1-9fd75b99d323
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_liouville_reduced_progression_squarefree_bilinear_bound
import Mathlib.NumberTheory.ArithmeticFunction.Liouville
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
This adapts the square-root truncation of Helfgott–Thompson, §2, (2.1), to Liouville coefficients.
The inverse kernel is the indicator of squarefree positive integers.
The weighted divisor-pair argument adapts the reindexing in Mathlib's
ArithmeticFunction.sum_Ioc_mul_eq_sum_sum (ArithmeticFunction/Misc.lean, Apache 2.0,
copyright 2020 Aaron Anderson). Only the final declaration uses the proposed cancellation estimate.
-/

open scoped BigOperators
open Finset

namespace LiouvilleProgression

abbrev lambda : ArithmeticFunction ℝ := ArithmeticFunction.liouville
noncomputable def squarefreeKernel : ArithmeticFunction ℝ :=
  ⟨fun k => if Squarefree k then 1 else 0, by simp⟩

private theorem kernel_twist (n : ℕ) :
    squarefreeKernel n = lambda n * (ArithmeticFunction.moebius n : ℝ) := by
  change (if Squarefree n then 1 else 0) =
    (ArithmeticFunction.liouville n : ℝ) * (ArithmeticFunction.moebius n : ℝ)
  by_cases h : Squarefree n
  · have heq : ArithmeticFunction.liouville n = ArithmeticFunction.moebius n := by
      rw [ArithmeticFunction.liouville_apply h.ne_zero, ArithmeticFunction.moebius_apply_of_squarefree h]
    rw [if_pos h, heq, ← sq, ← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree h]
    simp
  · simp [h]

-- Twisting the Möbius inverse relation by the completely multiplicative λ gives λ * μ² = 1.
theorem liouville_mul_squarefree : lambda * squarefreeKernel = 1 := by
  ext n
  let z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
  let m : ArithmeticFunction ℝ := ArithmeticFunction.moebius
  have hz : z * m = 1 := ArithmeticFunction.coe_zeta_mul_coe_moebius
  rw [ArithmeticFunction.mul_apply]
  calc
    _ = ∑ p ∈ n.divisorsAntidiagonal, lambda n * (z p.1 * m p.2) := by
      refine sum_congr rfl fun p hp => ?_
      obtain ⟨hp',hn⟩ := Nat.mem_divisorsAntidiagonal.mp hp
      have hfst : p.1 ≠ 0 := by intro h; simp [h] at hp'; exact hn hp'.symm
      have hz1 : z p.1 = 1 := by simp [z, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply_ne hfst]
      have hl : lambda n = lambda p.1 * lambda p.2 := by
        simp [← hp', lambda, ArithmeticFunction.intCoe_apply, ArithmeticFunction.liouville_apply_mul]
      rw [kernel_twist, hz1, hl, one_mul]
      change _ = _ * (ArithmeticFunction.moebius p.2 : ℝ)
      ring
    _ = lambda n * (z * m) n := by rw [ArithmeticFunction.mul_apply, mul_sum]
    _ = _ := by
      rw [hz, ArithmeticFunction.one_apply]
      by_cases h : n = 1 <;> simp [h, lambda, ArithmeticFunction.intCoe_apply,
        ArithmeticFunction.liouville_apply_one]

noncomputable def short (u : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k ≤ u then (ArithmeticFunction.liouville k : ℝ) else 0, by simp⟩

-- Two factors above the square-root cutoff cannot have product at most n.
private theorem tail_square_zero (n k : ℕ) (hk : k ≤ n) :
    ((lambda - short n.sqrt) * (lambda - short n.sqrt)) k = 0 := by
  rw [ArithmeticFunction.mul_apply]
  refine sum_eq_zero fun p hp => ?_
  obtain ⟨heq, _⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have hsmall : p.1 ≤ n.sqrt ∨ p.2 ≤ n.sqrt := by
    by_contra! h
    have hh := Nat.mul_le_mul h.1 h.2
    have hn := Nat.lt_succ_sqrt n
    omega
  change ((ArithmeticFunction.liouville p.1 : ℝ) - (if p.1 ≤ n.sqrt then _ else 0)) *
      ((ArithmeticFunction.liouville p.2 : ℝ) - (if p.2 ≤ n.sqrt then _ else 0)) = 0
  rcases hsmall with h | h <;> simp [h]

theorem truncated_coefficient (n k : ℕ) (hk : k ≤ n) :
    lambda k = short n.sqrt k + short n.sqrt k - (short n.sqrt * (short n.sqrt * squarefreeKernel)) k := by
  let s := short n.sqrt
  have hinv : lambda * squarefreeKernel = 1 := liouville_mul_squarefree
  have halg : (lambda - s) * (lambda - s) * squarefreeKernel = lambda - s - s + s * (s * squarefreeKernel) := by
    calc
      _ = lambda * (lambda * squarefreeKernel) - s * (lambda * squarefreeKernel) - s * (lambda * squarefreeKernel) + s * (s * squarefreeKernel) := by ring
      _ = _ := by rw [hinv]; simp
  have hzero : ((lambda - s) * (lambda - s) * squarefreeKernel) k = 0 := by
    rw [ArithmeticFunction.mul_apply]
    refine sum_eq_zero fun p hp => ?_
    obtain ⟨hprod, hk0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have hp1 : p.1 ≤ k := Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) ⟨p.2, hprod.symm⟩
    rw [show ((lambda - s) * (lambda - s)) p.1 = 0 from tail_square_zero n p.1 (hp1.trans hk), zero_mul]
  rw [halg] at hzero
  change lambda k - s k - s k + (s * (s * squarefreeKernel)) k = 0 at hzero
  change lambda k = s k + s k - (s * (s * squarefreeKernel)) k
  linarith

-- Weighted version of the divisor-pair reindexing in Mathlib's
-- ArithmeticFunction.sum_Ioc_mul_eq_sum_sum. The weight need not be multiplicative.
private theorem weighted_convolution (n : ℕ) (w : ℕ → ℝ) (f g : ArithmeticFunction ℝ) :
    (∑ k ∈ Ioc 0 n, w k * (f * g) k) =
    ∑ d ∈ Ioc 0 n, f d * ∑ e ∈ Ioc 0 (n / d), w (d * e) * g e := by
  classical
  let box := (Ioc 0 n) ×ˢ (Ioc 0 n)
  calc
    _ = ∑ k ∈ Ioc 0 n, ∑ p ∈ box, if p.1 * p.2 = k then
          w (p.1 * p.2) * (f p.1 * g p.2) else 0 := by
      refine sum_congr rfl fun k hk => ?_
      obtain ⟨hk0, hkn⟩ := mem_Ioc.mp hk
      rw [ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_eq_prod_filter_of_le hk0.ne' hkn,
        mul_sum, ← sum_filter]
      refine sum_congr rfl fun p hp => ?_
      rw [(mem_filter.mp hp).2]
    _ = ∑ p ∈ box, if p.1 * p.2 ≤ n then w (p.1 * p.2) * (f p.1 * g p.2) else 0 := by
      rw [sum_comm]
      refine sum_congr rfl fun p hp => ?_
      have hp' := mem_product.mp hp
      have hpos := Nat.mul_pos (mem_Ioc.mp hp'.1).1 (mem_Ioc.mp hp'.2).1
      simp [mem_Ioc, hpos]
    _ = _ := by
      rw [show box = _ from rfl, sum_product]
      refine sum_congr rfl fun d hd => ?_
      have hd0 := (mem_Ioc.mp hd).1
      rw [mul_sum]
      have heq : (Ioc 0 (n / d)) = (Ioc 0 n).filter (fun e => d * e ≤ n) := by
        ext e
        simp only [mem_Ioc, mem_filter]
        rw [Nat.le_div_iff_mul_le hd0, Nat.mul_comm e d]
        constructor
        · rintro ⟨he, h⟩
          exact ⟨⟨he, ((Nat.le_div_iff_mul_le hd0).mpr (by simpa [Nat.mul_comm] using h)).trans
            (Nat.div_le_self n d)⟩, h⟩
        · rintro ⟨⟨he, _⟩, h⟩
          exact ⟨he, h⟩
      rw [heq, sum_filter]
      apply sum_congr rfl
      intro e _
      dsimp only
      split_ifs <;> ring

private theorem truncate_sum (N u : ℕ) (hu : u ≤ N) (F : ℕ → ℝ) :
    (∑ k ∈ Ioc 0 N, short u k * F k) = ∑ k ∈ Ioc 0 u, lambda k * F k := by
  calc
    _ = ∑ k ∈ Ioc 0 u, short u k * F k := by
      symm
      apply sum_subset
      · intro k hk
        exact mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1, (mem_Ioc.mp hk).2.trans hu⟩
      · intro k hk hk'
        have h : ¬ k ≤ u := fun h => hk' (mem_Ioc.mpr ⟨(mem_Ioc.mp hk).1,h⟩)
        simp [short, h]
    _ = _ := by
      refine sum_congr rfl fun k hk => ?_
      simp [short, (mem_Ioc.mp hk).2, lambda]

noncomputable def residueWeight {q : ℕ} (a : ZMod q) (k : ℕ) : ℝ :=
  if (k : ZMod q) = a then 1 else 0

noncomputable def bilinear {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n.sqrt, lambda d * ∑ e ∈ Ioc 0 n.sqrt, lambda e *
    (((Ioc 0 (n / (d * e))).filter (fun r => Squarefree r ∧ ((d * e * r : ℕ) : ZMod q) = a)).card : ℝ)

theorem reindex_bilinear {q : ℕ} (a : ZMod q) (n : ℕ) :
    (∑ k ∈ Ioc 0 n, residueWeight a k * (short n.sqrt * (short n.sqrt * squarefreeKernel)) k) =
    bilinear a n := by
  rw [weighted_convolution, truncate_sum n _ (Nat.sqrt_le_self n)]
  refine sum_congr rfl fun d hd => ?_
  have hd' := mem_Ioc.mp hd
  have hu : n.sqrt ≤ n / d := (Nat.le_div_iff_mul_le hd'.1).mpr <|
    (Nat.mul_le_mul_left n.sqrt hd'.2).trans (Nat.sqrt_le n)
  congr 1
  rw [weighted_convolution (n / d) (fun k => residueWeight a (d * k)), truncate_sum _ _ hu]
  refine sum_congr rfl fun e _ => ?_
  congr 1
  rw [Nat.div_div_eq_div_mul, ← sum_boole]
  refine sum_congr rfl fun r hr => ?_
  by_cases hs : Squarefree r <;> by_cases h : ((d * e * r : ℕ) : ZMod q) = a <;>
    simp_all [residueWeight, squarefreeKernel, Nat.mul_assoc]

noncomputable def partialSum {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  ∑ k ∈ Ioc 0 n, lambda k * residueWeight a k

theorem weighted_identity {q : ℕ} (a : ZMod q) (n : ℕ) :
    partialSum a n = 2 * partialSum a n.sqrt - bilinear a n := by
  unfold partialSum
  rw [← reindex_bilinear, ← truncate_sum n _ (Nat.sqrt_le_self n)]
  rw [mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun k hk => ?_
  rw [truncated_coefficient n k (mem_Ioc.mp hk).2]
  ring

private theorem parent_sum {q : ℕ} (a : ZMod q) (n : ℕ) :
    (∑ k ∈ range (n + 1),
      if (k : ZMod q) = a then (ArithmeticFunction.liouville k : ℝ) else 0) = partialSum a n := by
  classical
  have hr : range (n + 1) = insert 0 (Ioc 0 n) := by
    ext k
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  rw [hr, sum_insert (by simp)]
  have hz : (ArithmeticFunction.liouville 0 : ℝ) = 0 := by simp
  simp only [hz, ite_self, zero_add]
  refine sum_congr rfl fun k _ => ?_
  simp only [residueWeight, lambda, ArithmeticFunction.intCoe_apply]
  split_ifs <;> simp_all

private theorem partialSum_abs_le {q : ℕ} (a : ZMod q) (u : ℕ) :
    |partialSum a u| ≤ (u : ℝ) := by
  unfold partialSum
  calc
    _ ≤ ∑ k ∈ Ioc 0 u, |lambda k * residueWeight a k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Ioc 0 u, (1 : ℝ) := by
      refine sum_le_sum fun k hkMem => ?_
      have hmu : |(ArithmeticFunction.liouville k : ℝ)| ≤ 1 := by
        have hk : k ≠ 0 := (mem_Ioc.mp hkMem).1.ne'
        simp [ArithmeticFunction.liouville_apply hk, abs_pow]
      by_cases h : (k : ZMod q) = a <;> simp [residueWeight, h, lambda, hmu]
    _ = _ := by simp

theorem short_bound {q : ℕ} (a : ZMod q) (n : ℕ) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) ≤ σ) : |partialSum a n.sqrt| ≤ ((n : ℝ) + 1) ^ σ := by
  calc
    _ ≤ (n.sqrt : ℝ) := partialSum_abs_le a n.sqrt
    _ ≤ Real.sqrt ((n : ℝ) + 1) := by
      apply (Real.le_sqrt (by positivity) (by positivity)).mpr
      have h : (n.sqrt : ℝ) ^ 2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
      linarith
    _ ≤ _ := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by simp) hhalf

theorem reduction (q : ℕ) (σ : ℝ) (hhalf : (1 / 2 : ℝ) ≤ σ)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ n : ℕ, |bilinear a n| ≤ C * ((n : ℝ) + 1) ^ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ n : ℕ,
      |∑ k ∈ range (n + 1), if (k : ZMod q) = a then (ArithmeticFunction.liouville k : ℝ) else 0|
        ≤ C * ((n : ℝ) + 1) ^ σ := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨2 + C, by positivity, fun a ha n => ?_⟩
  rw [parent_sum, weighted_identity]
  calc
    _ ≤ |2 * partialSum a n.sqrt| + |bilinear a n| := abs_sub _ _
    _ = 2 * |partialSum a n.sqrt| + |bilinear a n| := by rw [abs_mul]; norm_num
    _ ≤ 2 * (((n : ℝ) + 1) ^ σ) + C * ((n : ℝ) + 1) ^ σ :=
      add_le_add (mul_le_mul_of_nonneg_left (short_bound a n σ hhalf) (by norm_num)) (h a ha n)
    _ = _ := by ring

end LiouvilleProgression

open ArithmeticFunction Finset
theorem solution
    (q : ℕ) [NeZero q] (σ : ℝ) (hhalf : 1 / 2 < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ZMod q, IsUnit a → ∀ N : ℕ,
      |∑ j ∈ range (N+1), if (j:ZMod q)=a then (liouville j:ℝ) else 0| ≤ C*((N:ℝ)+1)^σ := by
  apply LiouvilleProgression.reduction q σ hhalf.le
  exact GRH.liouville_reduced_progression_squarefree_bilinear_bound q σ hhalf hone
