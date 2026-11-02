-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_C1_moving_base_exponential_polynomial_approx
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:57:34.619959+00:00
-- url     : https://prove2.me/submissions/96ccdf0d-cfa3-476a-8d07-aa4db187be28

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_derivative_exponential_compactification
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_Bernstein_zero_constant_polynomial_uniform_density
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_C1_derivative_moving_base_uniform_finite_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set Filter
open AvramDividend.Classical

/-! Uniform polynomial approximation of the translated C1 derivative on a
finite negative-jump band, with a simultaneous global polynomial bound. -/
private theorem local_poly (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ p : Polynomial ℝ, Polynomial.eval 0 p = 0 ∧
      (∀ r ∈ Icc (0 : ℝ) M,
        |Polynomial.eval (Real.exp (-r)) p - deriv w (x - r)| < ε) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        |Polynomial.eval t p| ≤ L + ε) := by
  obtain ⟨F, hFcont, hF0, hFbound, hFeq⟩ :=
    avram_wave5_04c_C1_derivative_exponential_compactification
      w hwC1 L hL hLip x M hM
  let f : C(unitInterval.Elem, ℝ) :=
    ⟨fun t => F (t : ℝ), hFcont.comp continuous_subtype_val⟩
  have hf0 : f 0 = 0 := by simpa [f] using hF0
  obtain ⟨p, hp0, hpError⟩ :=
    avram_wave5_04c_Bernstein_zero_constant_polynomial_uniform_density f hf0 ε hε
  refine ⟨p, hp0, ?_, ?_⟩
  · intro r hr
    have he : Real.exp (-r) ∈ Icc (0 : ℝ) 1 := by
      constructor
      · exact (Real.exp_pos _).le
      · exact Real.exp_le_one_iff.mpr (by linarith [hr.1])
    have hh := hpError (⟨Real.exp (-r), he⟩ : unitInterval.Elem)
    simpa only [f, ContinuousMap.coe_mk, Function.comp_apply, hFeq r hr] using hh
  · intro t ht
    have hh := hpError (⟨t, ht⟩ : unitInterval.Elem)
    have happrox : |Polynomial.eval t p - F t| < ε := by
      simpa only [f, ContinuousMap.coe_mk, Function.comp_apply] using hh
    have hbound := hFbound t ht
    calc
      |Polynomial.eval t p| =
          |(Polynomial.eval t p - F t) + F t| := by ring
      _ ≤ |Polynomial.eval t p - F t| + |F t| := abs_add_le _ _
      _ ≤ L + ε := by linarith

/-! One fixed exponential polynomial approximates the C1 derivative uniformly
on a finite jump-size band even when the physical-drift base moves slightly. -/
theorem solution (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x M ε : ℝ) (hM : 0 ≤ M) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ p : Polynomial ℝ,
      Polynomial.eval 0 p = 0 ∧
      (∀ b r : ℝ, |b - x| < δ → r ∈ Icc (0 : ℝ) M →
        |Polynomial.eval (Real.exp (-r)) p - deriv w (b - r)| < ε) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, |Polynomial.eval t p| ≤ L + ε) := by
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨p, hp0, hpApprox, hpBound⟩ :=
    local_poly w hwC1 L hL hLip x M (ε / 2) hM hhalf
  obtain ⟨δ, hδ, hMove⟩ :=
    avram_wave5_04c_C1_derivative_moving_base_uniform_finite_band w hwC1 x M (ε / 2) hM hhalf
  refine ⟨δ, hδ, p, hp0, ?_, ?_⟩
  · intro b r hb hr
    have ha := hpApprox r hr
    have hm := hMove b r hb hr
    calc
      |Polynomial.eval (Real.exp (-r)) p - deriv w (b - r)| =
          |(Polynomial.eval (Real.exp (-r)) p - deriv w (x - r)) +
             (deriv w (x - r) - deriv w (b - r))| := by ring
      _ ≤ |Polynomial.eval (Real.exp (-r)) p - deriv w (x - r)| +
          |deriv w (x - r) - deriv w (b - r)| := abs_add_le _ _
      _ < ε := by
        rw [abs_sub_comm] at hm
        linarith
  · intro t ht
    have hp := hpBound t ht
    linarith
