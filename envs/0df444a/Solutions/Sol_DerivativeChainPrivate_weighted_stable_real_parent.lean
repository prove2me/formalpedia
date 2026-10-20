-- Prove2me | solution 1 for DerivativeChainPrivate.weighted_stable_real_parent
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-19T05:02:19.857574+00:00
-- url     : https://prove2.me/submissions/635176c3-01c6-40a1-aed6-f8d37d9fc81f

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial



theorem weighted_derivative_factor (q : Polynomial ℝ) (r k : ℕ) :
    (X ^ (r + 1) * q ^ (k + 1)).derivative =
      X ^ r * q ^ k * (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative) := by
  simp only [derivative_mul, derivative_pow, derivative_X, mul_one,
    Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [pow_succ q k, pow_succ X r]
  ring











end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate

theorem card_real_roots_interval_le_derivative (p : Polynomial ℝ) (A B : ℝ) :
    (p.roots.filter (fun x => A ≤ x ∧ x ≤ B)).card ≤
      (p.derivative.roots.filter (fun x => A ≤ x ∧ x ≤ B)).card + 1 := by
  classical
  rcases eq_or_ne p.derivative 0 with hd | hd
  · rw [Polynomial.eq_C_of_derivative_eq_zero hd]
    simp
  have hp : p ≠ 0 := ne_of_apply_ne Polynomial.derivative (by rwa [Polynomial.derivative_zero])
  let s := p.roots.filter (fun x => A ≤ x ∧ x ≤ B)
  let t := p.derivative.roots.filter (fun x => A ≤ x ∧ x ≤ B)
  have hs (x : ℝ) (hx : x ∈ s.toFinset) : x ∈ p.roots ∧ (A ≤ x ∧ x ≤ B) := by
    simpa only [s, Multiset.mem_toFinset, Multiset.mem_filter] using hx
  have ht (x : ℝ) (hx : x ∈ t.toFinset) : x ∈ p.derivative.roots ∧ (A ≤ x ∧ x ≤ B) := by
    simpa only [t, Multiset.mem_toFinset, Multiset.mem_filter] using hx
  have hcard : s.toFinset.card ≤ (t.toFinset \ s.toFinset).card + 1 := by
    refine Finset.card_le_sdiff_of_interleaved ?_
    intro x hx y hy hxy _
    obtain ⟨z, hz, hzero⟩ := exists_deriv_eq_zero hxy p.continuousOn
      (((Polynomial.mem_roots hp).mp (hs x hx).1).trans
        ((Polynomial.mem_roots hp).mp (hs y hy).1).symm)
    refine ⟨z, ?_, hz⟩
    rw [Multiset.mem_toFinset, Multiset.mem_filter]
    refine ⟨?_, (hs x hx).2.1.trans hz.1.le, hz.2.le.trans (hs y hy).2.2⟩
    rwa [Polynomial.mem_roots hd, Polynomial.IsRoot, ← p.deriv]
  have hscount (x : ℝ) (hx : x ∈ s.toFinset) :
      s.count x = p.rootMultiplicity x := by
    dsimp [s]
    rw [Multiset.count_filter_of_pos (p := fun y : ℝ => A ≤ y ∧ y ≤ B)
      (a := x) (hs x hx).2, Polynomial.count_roots]
  have htcount (x : ℝ) (hx : x ∈ s.toFinset) :
      t.count x = p.derivative.rootMultiplicity x := by
    dsimp [t]
    rw [Multiset.count_filter_of_pos (p := fun y : ℝ => A ≤ y ∧ y ≤ B)
      (a := x) (hs x hx).2, Polynomial.count_roots]
  change s.card ≤ t.card + 1
  calc
    s.card = ∑ x ∈ s.toFinset, s.count x := (Multiset.toFinset_sum_count_eq _).symm
    _ = ∑ x ∈ s.toFinset, (s.count x - 1 + 1) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (Nat.sub_add_cancel (Nat.succ_le_iff.mpr
        (Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hx)))).symm
    _ = (∑ x ∈ s.toFinset, (p.rootMultiplicity x - 1)) + s.toFinset.card := by
      simp only [Finset.sum_add_distrib, Finset.card_eq_sum_ones]
      congr 1
      exact Finset.sum_congr rfl (fun x hx => by rw [hscount x hx])
    _ ≤ (∑ x ∈ s.toFinset, t.count x) + ((t.toFinset \ s.toFinset).card + 1) := by
      apply add_le_add _ hcard
      apply Finset.sum_le_sum
      intro x hx
      rw [htcount x hx]
      exact Polynomial.rootMultiplicity_sub_one_le_derivative_rootMultiplicity p x
    _ ≤ (∑ x ∈ s.toFinset, t.count x) +
        ((∑ x ∈ t.toFinset \ s.toFinset, t.count x) + 1) := by
      gcongr
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_le_sum
      intro x hx
      exact Nat.succ_le_iff.mpr (Multiset.count_pos.mpr
        (Multiset.mem_toFinset.mp (Finset.mem_sdiff.mp hx).1))
    _ = t.card + 1 := by
      rw [← add_assoc, ← Finset.sum_union Finset.disjoint_sdiff,
        Finset.union_sdiff_self_eq_union, ← Multiset.toFinset_sum_count_eq,
        ← Finset.sum_subset Finset.subset_union_right]
      intro x _ hx
      simpa only [Multiset.mem_toFinset, Multiset.count_eq_zero] using hx

theorem real_derivative_roots_interval_of_count_eq (p : Polynomial ℝ) (A B : ℝ)
    (hparent : ∀ x ∈ p.roots, A ≤ x ∧ x ≤ B)
    (hcount : p.roots.card = p.derivative.roots.card + 1) :
    ∀ x ∈ p.derivative.roots, A ≤ x ∧ x ≤ B := by
  classical
  have h := card_real_roots_interval_le_derivative p A B
  rw [Multiset.filter_eq_self.mpr hparent, hcount] at h
  have heq : p.derivative.roots.filter (fun x => A ≤ x ∧ x ≤ B) = p.derivative.roots := by
    apply Multiset.eq_of_le_of_card_le (Multiset.filter_le _ _)
    omega
  exact Multiset.filter_eq_self.mp heq

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem derivative_real_parents_of_count (p : Polynomial ℝ)
    (hcount : p.roots.card = p.derivative.roots.card + 1) (y : ℝ)
    (hy : y ∈ p.derivative.roots) :
    ∃ lo ∈ p.roots, ∃ hi ∈ p.roots, lo ≤ y ∧ y ≤ hi := by
  classical
  have hne : p.roots ≠ 0 := by intro h; simp [h] at hcount
  let s := p.roots.toFinset
  have hs : s.Nonempty := Multiset.toFinset_nonempty.mpr hne
  have h := real_derivative_roots_interval_of_count_eq p (s.min' hs) (s.max' hs)
    (fun x hx => ⟨Finset.min'_le _ x (Multiset.mem_toFinset.mpr hx),
      Finset.le_max' _ x (Multiset.mem_toFinset.mpr hx)⟩) hcount y hy
  exact ⟨s.min' hs, Multiset.mem_toFinset.mp (Finset.min'_mem _ hs),
    s.max' hs, Multiset.mem_toFinset.mp (Finset.max'_mem _ hs), h⟩



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate









end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution (q : Polynomial ℝ) (hq : q ≠ 0) (r k : ℕ)
    (hcount : (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative).roots.card =
      q.roots.card) (y : ℝ)
    (hy : (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative).eval y = 0)
    (hyne : y ≠ 0) :
    ∃ x ∈ q.roots, (0 < y ∧ y ≤ x) ∨ (y < 0 ∧ x ≤ y) := by
  classical
  let b := C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative
  let p : Polynomial ℝ := X ^ (r + 1) * q ^ (k + 1)
  have hfactor : p.derivative = X ^ r * q ^ k * b := weighted_derivative_factor q r k
  have hpdeg : p.natDegree = r + 1 + (k + 1) * q.natDegree := by
    dsimp [p]
    rw [natDegree_mul (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hq),
      natDegree_X_pow, natDegree_pow]
  have hd : p.derivative ≠ 0 := by
    intro h; have hz := Polynomial.derivative_eq_zero.mp h; rw [hpdeg] at hz; omega
  have hp : p ≠ 0 := mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hq)
  have hc : p.roots.card = p.derivative.roots.card + 1 := by
    rw [hfactor, roots_mul hp, roots_mul (by rw [← hfactor]; exact hd),
      roots_mul (mul_ne_zero (pow_ne_zero _ X_ne_zero) (pow_ne_zero _ hq))]
    simp only [Multiset.card_add, roots_pow, roots_X, Multiset.card_nsmul,
      Multiset.card_singleton, mul_one]
    have hb : b.roots.card = q.roots.card := hcount
    rw [hb]
    ring
  have hyd : y ∈ p.derivative.roots := by
    apply (Polynomial.mem_roots hd).mpr
    change p.derivative.eval y = 0
    rw [hfactor, eval_mul, show b.eval y = 0 from hy, mul_zero]
  obtain ⟨lo, hlo, hi, hhi, hloy, hyhi⟩ := derivative_real_parents_of_count p hc y hyd
  have hroot (x : ℝ) (hx : x ∈ p.roots) (hxne : x ≠ 0) : x ∈ q.roots := by
    have hz := Polynomial.isRoot_of_mem_roots hx
    change (X ^ (r + 1) * q ^ (k + 1)).eval x = 0 at hz
    simp only [eval_mul, eval_pow, eval_X] at hz
    have hpow := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hxne)
    exact (Polynomial.mem_roots hq).mpr (eq_zero_of_pow_eq_zero hpow)
  rcases lt_or_gt_of_ne hyne with hneg | hpos
  · exact ⟨lo, hroot lo hlo (by linarith), Or.inr ⟨hneg, hloy⟩⟩
  · exact ⟨hi, hroot hi hhi (by linarith), Or.inl ⟨hpos, hyhi⟩⟩
