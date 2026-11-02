-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_Bernstein_endpoint_weighted_polynomial_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:53:52.333195+00:00
-- url     : https://prove2.me/submissions/89576403-bded-4637-bcda-517508384ae7

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_Bernstein_zero_constant_polynomial_uniform_density
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Set Filter
open AvramDividend.Classical

/-! A polynomial with the exact endpoint zero approximates a continuous
compactified profile with a first-order weight at the endpoint. -/
theorem solution (G : C(unitInterval.Elem, ℝ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Q : Polynomial ℝ, Polynomial.eval 1 Q = 0 ∧
      ∀ t : unitInterval.Elem,
        |Polynomial.eval (t : ℝ) Q -
          (1 - (t : ℝ)) * G t| ≤
          ε * (1 - (t : ℝ)) := by
  let g : C(unitInterval.Elem, ℝ) :=
    G - ContinuousMap.const _ (G 0)
  have hg0 : g 0 = 0 := by simp [g]
  obtain ⟨p, hp0, hpApprox⟩ :=
    avram_wave5_04c_Bernstein_zero_constant_polynomial_uniform_density
      g hg0 ε hε
  let Q : Polynomial ℝ :=
    (1 - Polynomial.X) * (p + Polynomial.C (G 0))
  refine ⟨Q, ?_, ?_⟩
  · simp [Q]
  intro t
  have ht : (t : ℝ) ∈ Icc (0 : ℝ) 1 := t.property
  have ht1 : 0 ≤ 1 - (t : ℝ) := by linarith [ht.2]
  have hp := hpApprox t
  have happrox :
      |Polynomial.eval (t : ℝ) (p + Polynomial.C (G 0)) -
        G t| < ε := by
    have hh :
        Polynomial.eval (t : ℝ) (p + Polynomial.C (G 0)) -
          G t = Polynomial.eval (t : ℝ) p - g t := by
      simp only [g, ContinuousMap.sub_apply, ContinuousMap.const_apply,
        Polynomial.eval_add, Polynomial.eval_C]
      ring
    rw [hh]
    exact hp
  have hfactor :
      Polynomial.eval (t : ℝ) Q -
        (1 - (t : ℝ)) * G t =
      (1 - (t : ℝ)) *
        (Polynomial.eval (t : ℝ) (p + Polynomial.C (G 0)) - G t) := by
    simp [Q, Polynomial.eval_mul, Polynomial.eval_sub]
    ring
  rw [hfactor, abs_mul, abs_of_nonneg ht1]
  nlinarith [mul_le_mul_of_nonneg_left happrox.le ht1]
