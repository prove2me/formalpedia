-- Prove2me | solution 1 for DerivativeChainPrivate.spoke_geodesic
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:03:37.479263+00:00
-- url     : https://prove2.me/submissions/1e4d61d1-4c41-4bd5-a686-78beee9fefa1

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Theorems.Thm_DerivativeChainPrivate_real_splits_weighted_derivative
import Theorems.Thm_DerivativeChainPrivate_spoke_derivative_ray_parent
import Theorems.Thm_DerivativeChainPrivate_spoke_natDegree
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







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





theorem spoke_linear_root_zero (k r : ℕ) (q : Polynomial ℝ) (hk : 2 ≤ k)
    (hqne : q ≠ 0) (hdegree : (spokePoly k r q).natDegree = 1) :
    (spokePoly k r q).eval 0 = 0 := by
  have hdeg := spoke_natDegree k r q hqne (by omega)
  have hqdeg : q.natDegree = 0 := by nlinarith
  have hr : r = 1 := by rw [hqdeg, mul_zero, add_zero] at hdeg; omega
  simp [spokePoly, hr]

end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
open DerivativeChainPrivate
open Polynomial

theorem solution (n k r : ℕ) (q : Polynomial ℝ) (hk : 2 ≤ k)
    (hr : r < k) (hq : q.Splits) (hqne : q ≠ 0)
    (hdegree : (_root_.DerivativeChainPrivate.spokePoly k r q).natDegree = n + 1) :
    ∃ z : ℕ → ℂ, z 0 = 0 ∧
      (∀ i < n + 1, (Polynomial.derivative^[n - i] (_root_.DerivativeChainPrivate.spokePoly k r q)).eval (z i) = 0) ∧
      (∀ i < n, ‖z (i + 1) - z i‖ = ‖z (i + 1)‖ - ‖z i‖) := by
  induction n generalizing r q with
  | zero =>
    refine ⟨fun _ => 0, rfl, ?_, ?_⟩
    · intro i hi
      have : i = 0 := by omega
      subst i
      simpa using _root_.DerivativeChainPrivate.spoke_linear_root_zero k r q hk hqne hdegree
    · intro i hi; omega
  | succ n ih =>
    let p := _root_.DerivativeChainPrivate.spokePoly k r q
    have hpdeg : p.natDegree = n + 2 := by simpa [p, Nat.add_assoc] using hdegree
    obtain ⟨s, hs, v, hv, heq⟩ := _root_.DerivativeChainPrivate.spoke_derivative_closed k r q hk hr hq
    have hvne : v ≠ 0 := by
      intro hvzero
      have hp0 : p.derivative ≠ 0 := by
        intro h
        have := Polynomial.derivative_eq_zero.mp h
        omega
      apply hp0
      change (_root_.DerivativeChainPrivate.spokePoly k r q).derivative = 0
      rw [heq, hvzero]
      simp [_root_.DerivativeChainPrivate.spokePoly]
    have hvdeg : (_root_.DerivativeChainPrivate.spokePoly k s v).natDegree = n + 1 := by
      rw [← heq, Polynomial.natDegree_derivative]
      change p.natDegree - 1 = n + 1
      omega
    obtain ⟨z, hz0, hzroots, hzsteps⟩ := ih s v hs hv hvne hvdeg
    have hw : p.derivative.eval (z n) = 0 := by
      have h := hzroots n (by omega)
      simpa only [Nat.sub_self, Function.iterate_zero, id_eq, ← heq] using h
    obtain ⟨a, ha, hstep⟩ : ∃ a : ℂ, p.eval a = 0 ∧
        ‖a - z n‖ = ‖a‖ - ‖z n‖ := by
      by_cases hzero : z n = 0
      · obtain ⟨a, ha⟩ := Complex.exists_root (f := p)
          (Polynomial.natDegree_pos_iff_degree_pos.mp (by omega))
        exact ⟨a, ha, by simp [hzero]⟩
      · obtain ⟨t, ht, htroot⟩ :=
          _root_.DerivativeChainPrivate.spoke_derivative_ray_parent k r q hk hr hq hqne (by omega) (z n) hzero hw
        refine ⟨(t : ℂ) * z n, htroot, ?_⟩
        have ht0 : 0 ≤ t := by linarith
        have ht1 : 0 ≤ t - 1 := by linarith
        calc
          ‖(t : ℂ) * z n - z n‖ = ‖((t - 1 : ℝ) : ℂ) * z n‖ := by
            congr 1
            push_cast
            ring
          _ = (t - 1) * ‖z n‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht1]
          _ = ‖(t : ℂ) * z n‖ - ‖z n‖ := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
            ring
    let w (i : ℕ) := if i = n + 1 then a else z i
    refine ⟨w, by simp [w, hz0], ?_, ?_⟩
    · intro i hi
      by_cases hieq : i = n + 1
      · subst i
        simpa [w, p] using ha
      · have hin : i < n + 1 := by omega
        have h := hzroots i hin
        rw [← heq] at h
        have hexp : n + 1 - i = (n - i) + 1 := by omega
        simpa only [w, if_neg hieq, hexp, Function.iterate_succ_apply] using h
    · intro i hi
      by_cases hieq : i = n
      · subst i
        simpa [w] using hstep
      · have hin : i < n := by omega
        simpa [w, hieq, show i ≠ n + 1 by omega] using hzsteps i hin
