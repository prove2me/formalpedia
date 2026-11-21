-- Prove2me | solution 2 for GRH.moebius_partial_sum_reduced_progression_power_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @meadowlark
-- created : 2026-11-21T00:43:35.259031+00:00
-- url     : https://prove2.me/submissions/509e229b-7ae5-4fe8-b643-d32c7895621a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GRH_moebius_reduced_progression_bilinear_power_bound
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The coefficient identity follows Helfgott–Thompson, §2, (2.1), doi:10.1007/s40993-022-00408-8.
The weighted divisor-pair argument adapts the reindexing in Mathlib's
ArithmeticFunction.sum_Ioc_mul_eq_sum_sum (ArithmeticFunction/Misc.lean, Apache 2.0,
copyright 2020 Aaron Anderson). Only the final declaration uses the proposed child.
-/

open scoped BigOperators
open Finset

namespace MobiusProgression

abbrev mu : ArithmeticFunction ℝ := ArithmeticFunction.moebius
abbrev zeta : ArithmeticFunction ℝ := ArithmeticFunction.zeta

noncomputable def short (u : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k ≤ u then (ArithmeticFunction.moebius k : ℝ) else 0, by simp⟩

-- Two factors above the square-root cutoff cannot have product at most n.
private theorem tail_square_zero (n k : ℕ) (hk : k ≤ n) :
    ((mu - short n.sqrt) * (mu - short n.sqrt)) k = 0 := by
  rw [ArithmeticFunction.mul_apply]
  refine sum_eq_zero fun p hp => ?_
  obtain ⟨heq, _⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have hsmall : p.1 ≤ n.sqrt ∨ p.2 ≤ n.sqrt := by
    by_contra! h
    have hh := Nat.mul_le_mul h.1 h.2
    have hn := Nat.lt_succ_sqrt n
    omega
  change ((ArithmeticFunction.moebius p.1 : ℝ) - (if p.1 ≤ n.sqrt then _ else 0)) *
      ((ArithmeticFunction.moebius p.2 : ℝ) - (if p.2 ≤ n.sqrt then _ else 0)) = 0
  rcases hsmall with h | h <;> simp [h]

theorem truncated_coefficient (n k : ℕ) (hk : k ≤ n) :
    mu k = short n.sqrt k + short n.sqrt k - (short n.sqrt * (short n.sqrt * zeta)) k := by
  let s := short n.sqrt
  have hinv : mu * zeta = 1 := ArithmeticFunction.coe_moebius_mul_coe_zeta
  have halg : (mu - s) * (mu - s) * zeta = mu - s - s + s * (s * zeta) := by
    calc
      _ = mu * (mu * zeta) - s * (mu * zeta) - s * (mu * zeta) + s * (s * zeta) := by ring
      _ = _ := by rw [hinv]; simp
  have hzero : ((mu - s) * (mu - s) * zeta) k = 0 := by
    rw [ArithmeticFunction.coe_mul_zeta_apply]
    refine sum_eq_zero fun d hd => tail_square_zero n d ?_
    obtain ⟨hdvd,hk0⟩ := Nat.mem_divisors.mp hd
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hdvd).trans hk
  rw [halg] at hzero
  change mu k - s k - s k + (s * (s * zeta)) k = 0 at hzero
  change mu k = s k + s k - (s * (s * zeta)) k
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
    (∑ k ∈ Ioc 0 N, short u k * F k) = ∑ k ∈ Ioc 0 u, mu k * F k := by
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
      simp [short, (mem_Ioc.mp hk).2, mu]

noncomputable def residueWeight {q : ℕ} (a : ZMod q) (k : ℕ) : ℝ :=
  if (k : ZMod q) = a then 1 else 0

noncomputable def bilinear {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 n.sqrt, mu d * ∑ e ∈ Ioc 0 n.sqrt, mu e *
    (((Ioc 0 (n / (d * e))).filter (fun r => ((d * e * r : ℕ) : ZMod q) = a)).card : ℝ)

theorem reindex_bilinear {q : ℕ} (a : ZMod q) (n : ℕ) :
    (∑ k ∈ Ioc 0 n, residueWeight a k * (short n.sqrt * (short n.sqrt * zeta)) k) =
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
  have hr0 := (mem_Ioc.mp hr).1.ne'
  simp [residueWeight, zeta, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply_ne hr0, Nat.mul_assoc]

noncomputable def partialSum {q : ℕ} (a : ZMod q) (n : ℕ) : ℝ :=
  ∑ k ∈ Ioc 0 n, mu k * residueWeight a k

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
      if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0) = partialSum a n := by
  classical
  have hr : range (n + 1) = insert 0 (Ioc 0 n) := by
    ext k
    simp only [mem_range, mem_insert, mem_Ioc]
    omega
  rw [hr, sum_insert (by simp)]
  have hz : (ArithmeticFunction.moebius 0 : ℝ) = 0 := by simp
  simp only [hz, ite_self, zero_add]
  refine sum_congr rfl fun k _ => ?_
  simp only [residueWeight, mu, ArithmeticFunction.intCoe_apply]
  split_ifs <;> simp_all

private theorem partialSum_abs_le {q : ℕ} (a : ZMod q) (u : ℕ) :
    |partialSum a u| ≤ (u : ℝ) := by
  unfold partialSum
  calc
    _ ≤ ∑ k ∈ Ioc 0 u, |mu k * residueWeight a k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Ioc 0 u, (1 : ℝ) := by
      refine sum_le_sum fun k _ => ?_
      have hmu : |(ArithmeticFunction.moebius k : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k))
      by_cases h : (k : ZMod q) = a <;> simp [residueWeight, h, mu, hmu]
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

theorem reduction {q : ℕ} (a : ZMod q) (σ : ℝ) (hhalf : (1 / 2 : ℝ) ≤ σ)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |bilinear a n| ≤ C * ((n : ℝ) + 1) ^ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |∑ k ∈ range (n + 1), if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0|
        ≤ C * ((n : ℝ) + 1) ^ σ := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨2 + C, by positivity, fun n => ?_⟩
  rw [parent_sum, weighted_identity]
  calc
    _ ≤ |2 * partialSum a n.sqrt| + |bilinear a n| := abs_sub _ _
    _ = 2 * |partialSum a n.sqrt| + |bilinear a n| := by rw [abs_mul]; norm_num
    _ ≤ 2 * (((n : ℝ) + 1) ^ σ) + C * ((n : ℝ) + 1) ^ σ :=
      add_le_add (mul_le_mul_of_nonneg_left (short_bound a n σ hhalf) (by norm_num)) (h n)
    _ = _ := by ring

end MobiusProgression

theorem solution
    (q : ℕ) [NeZero q] (a : ZMod q) (ha : IsUnit a) (σ : ℝ)
    (hhalf : (1 / 2 : ℝ) < σ) (hone : σ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |∑ k ∈ Finset.range (n + 1),
        if (k : ZMod q) = a then (ArithmeticFunction.moebius k : ℝ) else 0| ≤
          C * ((n : ℝ) + 1) ^ σ := by
  apply MobiusProgression.reduction a σ hhalf.le
  exact GRH.moebius_reduced_progression_bilinear_power_bound q a ha σ hhalf hone
