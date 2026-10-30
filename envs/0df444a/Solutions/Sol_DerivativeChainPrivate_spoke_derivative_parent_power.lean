-- Prove2me | solution 1 for DerivativeChainPrivate.spoke_derivative_parent_power
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:59:54.08737+00:00
-- url     : https://prove2.me/submissions/7731e624-7bdc-4f52-9de0-e053de6cbae3

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Theorems.Thm_DerivativeChainPrivate_derivative_negative_parent
import Theorems.Thm_DerivativeChainPrivate_derivative_positive_parent
import Theorems.Thm_DerivativeChainPrivate_real_splits_weighted_derivative
import Theorems.Thm_DerivativeChainPrivate_spoke_natDegree
import Theorems.Thm_DerivativeChainPrivate_weighted_negative_parent
import Theorems.Thm_DerivativeChainPrivate_weighted_positive_parent
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial

theorem real_splits_derivative (p : Polynomial ℝ) (hp : p.Splits) :
    p.derivative.Splits := by
  apply Polynomial.splits_iff_card_roots.mpr
  have hcount := p.card_roots_le_derivative
  have hdegree := Polynomial.natDegree_derivative p
  have hbound := Polynomial.card_roots' p.derivative
  have hsplit := hp.natDegree_eq_card_roots
  omega













end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial



theorem spoke_derivative_succ (k r : ℕ) (q : Polynomial ℝ) :
    (spokePoly (k + 1) (r + 1) q).derivative =
      spokePoly (k + 1) r
        (C (r + 1 : ℝ) * q + C (k + 1 : ℝ) * X * q.derivative) := by
  simp only [spokePoly, derivative_mul, derivative_pow, derivative_X, mul_one,
    Nat.add_sub_cancel, derivative_comp, derivative_map, Polynomial.map_add,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Polynomial.add_comp,
    Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
  rw [pow_succ (X : Polynomial ℂ) r, pow_succ (X : Polynomial ℂ) k]
  simp only [map_add, map_natCast, map_one]
  push_cast
  ring

theorem spoke_derivative_zero (k : ℕ) (q : Polynomial ℝ) :
    (spokePoly (k + 1) 0 q).derivative =
      spokePoly (k + 1) k (C (k + 1 : ℝ) * q.derivative) := by
  simp only [spokePoly, pow_zero, one_mul, derivative_comp, derivative_pow,
    derivative_X, mul_one, Nat.add_sub_cancel, derivative_map,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.mul_comp, Polynomial.C_comp]
  simp only [map_add, map_natCast, map_one]
  push_cast
  ring



theorem spoke_derivative_closed (k r : ℕ) (q : Polynomial ℝ) (hk : 2 ≤ k)
    (hr : r < k) (hq : q.Splits) :
    ∃ s < k, ∃ v : Polynomial ℝ, v.Splits ∧
      (spokePoly k r q).derivative = spokePoly k s v := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  cases r with
  | zero =>
    exact ⟨j, by omega, C (j + 1 : ℝ) * q.derivative,
      (real_splits_derivative q hq).C_mul _, spoke_derivative_zero j q⟩
  | succ s =>
    exact ⟨s, by omega, C (s + 1 : ℝ) * q + C (j + 1 : ℝ) * X * q.derivative,
      real_splits_weighted_derivative q hq s j, spoke_derivative_succ j s q⟩

theorem spoke_eval_real_power (k r : ℕ) (q : Polynomial ℝ) (w : ℂ) (y : ℝ)
    (hw : w ^ k = (y : ℂ)) :
    (spokePoly k r q).eval w = w ^ r * ((q.eval y : ℝ) : ℂ) := by
  simp only [spokePoly, eval_mul, eval_pow, eval_X, eval_comp, hw]
  exact congrArg (fun z : ℂ => w ^ r * z)
    (Polynomial.eval_map_apply (f := Complex.ofRealHom) (p := q) y)



theorem spoke_root_power_real (k r : ℕ) (q : Polynomial ℝ) (hq : q.Splits)
    (hqne : q ≠ 0) (w : ℂ) (hw : w ≠ 0) (hz : (spokePoly k r q).eval w = 0) :
    ∃ y : ℝ, w ^ k = (y : ℂ) := by
  have heval : (q.map Complex.ofRealHom).eval (w ^ k) = 0 := by
    simp only [spokePoly, eval_mul, eval_pow, eval_X, eval_comp] at hz
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hw)
  obtain ⟨y, hy⟩ := hq.mem_range_of_isRoot hqne heval
  exact ⟨y, hy.symm⟩

end DerivativeChainPrivate



set_option autoImplicit false
open DerivativeChainPrivate
open Polynomial

theorem solution (k r : ℕ) (q : Polynomial ℝ)
    (hk : 2 ≤ k) (hr : r < k) (hq : q.Splits) (hqne : q ≠ 0)
    (hdegree : 2 ≤ (_root_.DerivativeChainPrivate.spokePoly k r q).natDegree) (w : ℂ) (hw : w ≠ 0)
    (hz : (_root_.DerivativeChainPrivate.spokePoly k r q).derivative.eval w = 0) :
    ∃ y x : ℝ, w ^ k = (y : ℂ) ∧ q.eval x = 0 ∧
      ((0 < y ∧ y ≤ x) ∨ (y < 0 ∧ x ≤ y)) := by
  obtain ⟨s, hs, v, hv, heq⟩ := _root_.DerivativeChainPrivate.spoke_derivative_closed k r q hk hr hq
  have hvne : v ≠ 0 := by
    intro hvzero
    have hdne : (_root_.DerivativeChainPrivate.spokePoly k r q).derivative ≠ 0 := by
      intro h
      have := Polynomial.derivative_eq_zero.mp h
      omega
    apply hdne
    rw [heq, hvzero]
    simp [_root_.DerivativeChainPrivate.spokePoly]
  obtain ⟨y, hy⟩ := _root_.DerivativeChainPrivate.spoke_root_power_real k s v hv hvne w hw (by rwa [← heq])
  have hyne : y ≠ 0 := by
    intro hzero
    have : w ^ k = 0 := by simp [hy, hzero]
    exact pow_ne_zero k hw this
  have hchild (b : Polynomial ℝ) (t : ℕ)
      (h : (_root_.DerivativeChainPrivate.spokePoly k t b).eval w = 0) : b.eval y = 0 := by
    rw [_root_.DerivativeChainPrivate.spoke_eval_real_power k t b w y hy] at h
    have hc := (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hw)
    exact Complex.ofReal_eq_zero.mp hc
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  cases r with
  | zero =>
    have hd : q.derivative.eval y = 0 := by
      rw [_root_.DerivativeChainPrivate.spoke_derivative_zero] at hz
      have ht := hchild (C (j + 1 : ℝ) * q.derivative) j hz
      simp only [eval_mul, eval_C] at ht
      exact (mul_eq_zero.mp ht).resolve_left (by positivity)
    have hqdeg : 0 < q.natDegree := by
      rw [_root_.DerivativeChainPrivate.spoke_natDegree _ _ _ hqne (by omega)] at hdegree
      by_contra h
      have : q.natDegree = 0 := by omega
      simp [this] at hdegree
    rcases lt_or_gt_of_ne hyne with hneg | hpos
    · obtain ⟨x, hx, hxy⟩ := _root_.DerivativeChainPrivate.derivative_negative_parent q hqne hq hqdeg y hd
      exact ⟨y, x, hy, (Polynomial.mem_roots hqne).mp hx, Or.inr ⟨hneg, hxy⟩⟩
    · obtain ⟨x, hx, hxy⟩ := _root_.DerivativeChainPrivate.derivative_positive_parent q hqne hq hqdeg y hd
      exact ⟨y, x, hy, (Polynomial.mem_roots hqne).mp hx, Or.inl ⟨hpos, hxy⟩⟩
  | succ t =>
    rw [_root_.DerivativeChainPrivate.spoke_derivative_succ] at hz
    have ht := hchild (C (t + 1 : ℝ) * q + C (j + 1 : ℝ) * X * q.derivative) t hz
    rcases lt_or_gt_of_ne hyne with hneg | hpos
    · obtain ⟨x, hx, hxy⟩ := _root_.DerivativeChainPrivate.weighted_negative_parent q hqne hq t j y hneg ht
      exact ⟨y, x, hy, (Polynomial.mem_roots hqne).mp hx, Or.inr ⟨hneg, hxy⟩⟩
    · obtain ⟨x, hx, hxy⟩ := _root_.DerivativeChainPrivate.weighted_positive_parent q hqne hq t j y hpos ht
      exact ⟨y, x, hy, (Polynomial.mem_roots hqne).mp hx, Or.inl ⟨hpos, hxy⟩⟩
